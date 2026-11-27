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

namespace RACert.S4N1.C0.S102

open RACert RACert.Problem

theorem cover28141 : P.CoversSplit 24 10 28141 0xff00ff00ea00a0000000000000000000ff000000000000000000000000000000ff00ff00ea00a0000000000000000000ff000000000000000000000000000000ff00ff00ea00a0000000000000000000ff0005000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 858, 865, 915, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c28141_0 : P.sumLeaves 24 28816384 1024 = 39180926 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28141) (lo := 0) (len := 1024) (W := 39180926) check rows elimOK (by decide) (by decide) cover28141 (by decide)
  decide +kernel

theorem h28141 : P.leaf 34 28141 = 39180926 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 39180926)]) (.cons c28141_0 (.nil)) (by decide) (by decide))

theorem cover28142 : P.CoversSplit 24 10 28142 0xff00ff00fa00fa000000000000000000ff000000000000000000000000000000ee0cee0cea08ea08ccccccccc8c8c8c8ee0c000000000000cccc000000000000ff00ff00fa00fa000000000000000000ff0005000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 522, 858, 865, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c28142_0 : P.sumLeaves 24 28817408 745 = 22804085 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28142) (lo := 0) (len := 745) (W := 22804085) check rows elimOK (by decide) (by decide) cover28142 (by decide)
  decide +kernel

theorem c28142_1 : P.sumLeaves 24 28818153 279 = 48318361 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28142) (lo := 745) (len := 279) (W := 48318361) check rows elimOK (by decide) (by decide) cover28142 (by decide)
  decide +kernel

theorem h28142 : P.leaf 34 28142 = 71122446 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(745, 22804085), (279, 48318361)]) (.cons c28142_0 (.cons c28142_1 (.nil))) (by decide) (by decide))

theorem cover28143 : P.CoversSplit 24 10 28143 0xff00ff00fa00fa000000000000000000ff000000000000000000000000000000ff00ff00fa00fa000000000000000000ff000000000000000000000000000000ff00ff00fa00fa000000000000000000ff0005000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 858, 865, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c28143_0 : P.sumLeaves 24 28818432 1002 = 89480455 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28143) (lo := 0) (len := 1002) (W := 89480455) check rows elimOK (by decide) (by decide) cover28143 (by decide)
  decide +kernel

theorem c28143_1 : P.sumLeaves 24 28819434 22 = 34564722 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28143) (lo := 1002) (len := 22) (W := 34564722) check rows elimOK (by decide) (by decide) cover28143 (by decide)
  decide +kernel

theorem h28143 : P.leaf 34 28143 = 124045177 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1002, 89480455), (22, 34564722)]) (.cons c28143_0 (.cons c28143_1 (.nil))) (by decide) (by decide))

theorem cover28158 : P.CoversSplit 24 10 28158 0xfffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafaffc0ffc0fac0fac0cc00cc00c800c800ffc0ffc0fac0fac0cc00cc00c800c800fffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafaffc0ffc0fac0fac0cc00cc00c800c800ffc0ffc0fac0fac0cc00cc00c800c800 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 858, 865, 1202, 1259, 1601]) (by decide +kernel)

theorem c28158_0 : P.sumLeaves 24 28833792 252 = 32487482 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28158) (lo := 0) (len := 252) (W := 32487482) check rows elimOK (by decide) (by decide) cover28158 (by decide)
  decide +kernel

theorem c28158_1 : P.sumLeaves 24 28834044 112 = 35204765 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28158) (lo := 252) (len := 112) (W := 35204765) check rows elimOK (by decide) (by decide) cover28158 (by decide)
  decide +kernel

theorem c28158_2 : P.sumLeaves 24 28834156 112 = 70633547 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28158) (lo := 364) (len := 112) (W := 70633547) check rows elimOK (by decide) (by decide) cover28158 (by decide)
  decide +kernel

theorem c28158_3 : P.sumLeaves 24 28834268 222 = 86550487 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28158) (lo := 476) (len := 222) (W := 86550487) check rows elimOK (by decide) (by decide) cover28158 (by decide)
  decide +kernel

theorem c28158_4 : P.sumLeaves 24 28834490 135 = 111437568 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28158) (lo := 698) (len := 135) (W := 111437568) check rows elimOK (by decide) (by decide) cover28158 (by decide)
  decide +kernel

theorem c28158_5 : P.sumLeaves 24 28834625 111 = 128250770 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28158) (lo := 833) (len := 111) (W := 128250770) check rows elimOK (by decide) (by decide) cover28158 (by decide)
  decide +kernel

theorem c28158_6 : P.sumLeaves 24 28834736 80 = 176852888 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28158) (lo := 944) (len := 80) (W := 176852888) check rows elimOK (by decide) (by decide) cover28158 (by decide)
  decide +kernel

theorem h28158 : P.leaf 34 28158 = 641417507 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(252, 32487482), (112, 35204765), (112, 70633547), (222, 86550487), (135, 111437568), (111, 128250770), (80, 176852888)]) (.cons c28158_0 (.cons c28158_1 (.cons c28158_2 (.cons c28158_3 (.cons c28158_4 (.cons c28158_5 (.cons c28158_6 (.nil)))))))) (by decide) (by decide))

theorem cover28159 : P.CoversSplit 24 10 28159 0xfffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafaffccffccfac8fac8ccccccccc8c8c8c8ffccffccfac8fac8ccccccccc8c8c8c8fffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafaffccffccfac8fac8ccccccccc8c8c8c8ffccffccfac8fac8ccccccccc8c8c8c8 :=
  coversSplit check rows (by decide) (by decide) (xs := [858, 865, 1202, 1259, 1601]) (by decide +kernel)

theorem c28159_0 : P.sumLeaves 24 28834816 190 = 70349409 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28159) (lo := 0) (len := 190) (W := 70349409) check rows elimOK (by decide) (by decide) cover28159 (by decide)
  decide +kernel

theorem c28159_1 : P.sumLeaves 24 28835006 126 = 100936479 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28159) (lo := 190) (len := 126) (W := 100936479) check rows elimOK (by decide) (by decide) cover28159 (by decide)
  decide +kernel

theorem c28159_2 : P.sumLeaves 24 28835132 112 = 107801117 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28159) (lo := 316) (len := 112) (W := 107801117) check rows elimOK (by decide) (by decide) cover28159 (by decide)
  decide +kernel

theorem c28159_3 : P.sumLeaves 24 28835244 134 = 173463640 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28159) (lo := 428) (len := 134) (W := 173463640) check rows elimOK (by decide) (by decide) cover28159 (by decide)
  decide +kernel

theorem c28159_4 : P.sumLeaves 24 28835378 176 = 190894634 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28159) (lo := 562) (len := 176) (W := 190894634) check rows elimOK (by decide) (by decide) cover28159 (by decide)
  decide +kernel

theorem c28159_5 : P.sumLeaves 24 28835554 116 = 182855646 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28159) (lo := 738) (len := 116) (W := 182855646) check rows elimOK (by decide) (by decide) cover28159 (by decide)
  decide +kernel

theorem c28159_6 : P.sumLeaves 24 28835670 107 = 254599301 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28159) (lo := 854) (len := 107) (W := 254599301) check rows elimOK (by decide) (by decide) cover28159 (by decide)
  decide +kernel

theorem c28159_7 : P.sumLeaves 24 28835777 63 = 204684098 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28159) (lo := 961) (len := 63) (W := 204684098) check rows elimOK (by decide) (by decide) cover28159 (by decide)
  decide +kernel

theorem h28159 : P.leaf 34 28159 = 1285584324 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(190, 70349409), (126, 100936479), (112, 107801117), (134, 173463640), (176, 190894634), (116, 182855646), (107, 254599301), (63, 204684098)]) (.cons c28159_0 (.cons c28159_1 (.cons c28159_2 (.cons c28159_3 (.cons c28159_4 (.cons c28159_5 (.cons c28159_6 (.cons c28159_7 (.nil))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(28141, 24), (28142, 48), (28143, 48), (28158, 24), (28159, 24)]

theorem segOK : checkSeg 16 perms 28141 28603 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 28141 28603 168 56556432072 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 56556432072)
    (SegSum.cons (w := 24) h28141 (SegSum.cons (w := 48) h28142 (SegSum.cons (w := 48) h28143 (SegSum.cons (w := 24) h28158 (SegSum.cons (w := 24) h28159 (show SegSum (P.leaf 34) [] 0 from rfl)))))) (by decide)

end RACert.S4N1.C0.S102
