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

namespace RACert.S6N0.C0.S66

open RACert RACert.Problem

theorem cover89054 : P.CoversSplit 26 10 89054 0xffff0000fffc0504ffff0000fffc0500ffff0000fffc0500fafa0000c8c800000505050505040504000000000000000005050505050405000000000000000000ffff0000ffcc0504ffff0000ffcc0500ffff0000cc000400fafa0000c80000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 874, 922, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89054_0 : P.sumLeaves 26 91191296 511 = 69557988 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89054) (lo := 0) (len := 511) (W := 69557988) check rows elimOK (by decide) (by decide) cover89054 (by decide)
  decide +kernel

theorem c89054_1 : P.sumLeaves 26 91191807 435 = 79945965 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89054) (lo := 511) (len := 435) (W := 79945965) check rows elimOK (by decide) (by decide) cover89054 (by decide)
  decide +kernel

theorem c89054_2 : P.sumLeaves 26 91192242 78 = 134635432 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89054) (lo := 946) (len := 78) (W := 134635432) check rows elimOK (by decide) (by decide) cover89054 (by decide)
  decide +kernel

theorem h89054 : P.leaf 36 89054 = 284139385 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(511, 69557988), (435, 79945965), (78, 134635432)]) (.cons c89054_0 (.cons c89054_1 (.cons c89054_2 (.nil)))) (by decide) (by decide))

theorem cover89055 : P.CoversSplit 26 10 89055 0xffff0000fffc0504ffff0000fffc0500ffff0000fffc0500fafa0000c8c800000505050505040504000000000000000005050505050405000000000000000000ffff0000ffcc0504ffff0000ffcc0500ffff0000cc000400fafa0000c80000000505050505040504000000000000000005050505040004000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 922, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89055_0 : P.sumLeaves 26 91192320 471 = 106796582 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89055) (lo := 0) (len := 471) (W := 106796582) check rows elimOK (by decide) (by decide) cover89055 (by decide)
  decide +kernel

theorem c89055_1 : P.sumLeaves 26 91192791 419 = 223059646 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89055) (lo := 471) (len := 419) (W := 223059646) check rows elimOK (by decide) (by decide) cover89055 (by decide)
  decide +kernel

theorem c89055_2 : P.sumLeaves 26 91193210 134 = 355650618 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89055) (lo := 890) (len := 134) (W := 355650618) check rows elimOK (by decide) (by decide) cover89055 (by decide)
  decide +kernel

theorem h89055 : P.leaf 36 89055 = 685506846 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(471, 106796582), (419, 223059646), (134, 355650618)]) (.cons c89055_0 (.cons c89055_1 (.cons c89055_2 (.nil)))) (by decide) (by decide))

theorem cover89069 : P.CoversSplit 26 10 89069 0xfffffffffffcfaf8fffffffafffcfaf8fffffffffffcfac8fafafafac8c8c8c8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [922, 923, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89069_0 : P.sumLeaves 26 91206656 905 = 4750402 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89069) (lo := 0) (len := 905) (W := 4750402) check rows elimOK (by decide) (by decide) cover89069 (by decide)
  decide +kernel

theorem c89069_1 : P.sumLeaves 26 91207561 108 = 6894792 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89069) (lo := 905) (len := 108) (W := 6894792) check rows elimOK (by decide) (by decide) cover89069 (by decide)
  decide +kernel

theorem c89069_2 : P.sumLeaves 26 91207669 11 = 1269648 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89069) (lo := 1013) (len := 11) (W := 1269648) check rows elimOK (by decide) (by decide) cover89069 (by decide)
  decide +kernel

theorem h89069 : P.leaf 36 89069 = 12914842 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(905, 4750402), (108, 6894792), (11, 1269648)]) (.cons c89069_0 (.cons c89069_1 (.cons c89069_2 (.nil)))) (by decide) (by decide))

theorem cover89070 : P.CoversSplit 26 10 89070 0xfffffffffffcfaf8fffffffafffcfaf8fffffffffffcfac8fafafafac8c8c8c80000000000000000000000000000000000000000000000000000000000000000ffffffffffccfac8fffffffaffccfac8ffffffff00000000fafafafa000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [874, 922, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89070_0 : P.sumLeaves 26 91207680 437 = 2966312 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89070) (lo := 0) (len := 437) (W := 2966312) check rows elimOK (by decide) (by decide) cover89070 (by decide)
  decide +kernel

theorem c89070_1 : P.sumLeaves 26 91208117 391 = 7965314 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89070) (lo := 437) (len := 391) (W := 7965314) check rows elimOK (by decide) (by decide) cover89070 (by decide)
  decide +kernel

theorem c89070_2 : P.sumLeaves 26 91208508 114 = 11275284 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89070) (lo := 828) (len := 114) (W := 11275284) check rows elimOK (by decide) (by decide) cover89070 (by decide)
  decide +kernel

theorem c89070_3 : P.sumLeaves 26 91208622 82 = 21833200 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89070) (lo := 942) (len := 82) (W := 21833200) check rows elimOK (by decide) (by decide) cover89070 (by decide)
  decide +kernel

theorem h89070 : P.leaf 36 89070 = 44040110 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(437, 2966312), (391, 7965314), (114, 11275284), (82, 21833200)]) (.cons c89070_0 (.cons c89070_1 (.cons c89070_2 (.cons c89070_3 (.nil))))) (by decide) (by decide))

theorem cover89071 : P.CoversSplit 26 10 89071 0xfffffffffffcfaf8fffffffafffcfaf8fffffffffffcfac8fafafafac8c8c8c80000000000000000000000000000000000000000000000000000000000000000ffffffffffccfac8fffffffaffccfac8ffffffff00000000fafafafa000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [922, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89071_0 : P.sumLeaves 26 91208704 437 = 13092254 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89071) (lo := 0) (len := 437) (W := 13092254) check rows elimOK (by decide) (by decide) cover89071 (by decide)
  decide +kernel

theorem c89071_1 : P.sumLeaves 26 91209141 391 = 22321634 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89071) (lo := 437) (len := 391) (W := 22321634) check rows elimOK (by decide) (by decide) cover89071 (by decide)
  decide +kernel

theorem c89071_2 : P.sumLeaves 26 91209532 114 = 40833004 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89071) (lo := 828) (len := 114) (W := 40833004) check rows elimOK (by decide) (by decide) cover89071 (by decide)
  decide +kernel

theorem c89071_3 : P.sumLeaves 26 91209646 82 = 45303436 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89071) (lo := 942) (len := 82) (W := 45303436) check rows elimOK (by decide) (by decide) cover89071 (by decide)
  decide +kernel

theorem h89071 : P.leaf 36 89071 = 121550328 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(437, 13092254), (391, 22321634), (114, 40833004), (82, 45303436)]) (.cons c89071_0 (.cons c89071_1 (.cons c89071_2 (.cons c89071_3 (.nil))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(89054, 720), (89055, 720), (89069, 360), (89070, 720), (89071, 720)]

theorem segOK : checkSeg 20 perms 89054 89086 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 89054 89086 3240 822019744800 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 822019744800)
    (SegSum.cons (w := 720) h89054 (SegSum.cons (w := 720) h89055 (SegSum.cons (w := 360) h89069 (SegSum.cons (w := 720) h89070 (SegSum.cons (w := 720) h89071 (show SegSum (P.leaf 36) [] 0 from rfl)))))) (by decide)

end RACert.S6N0.C0.S66
