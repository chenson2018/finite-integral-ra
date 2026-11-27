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

namespace RACert.S4N1.C0.S104

open RACert RACert.Problem

theorem cover28652 : P.CoversSplit 24 10 28652 0xffffffffeaeaaaaaffffffffeaeaaaaaffffffffeaeaaaaaffffffffeaeaaaaaeecceecceac8aa88ccccccccc8c88888eecceecceac8aa88ccccccccc8c88888ffffffffeaeaaaaaffff0000eaea0000ffffffffeaeaaaaaffff0000eaea0000eecc0000eac80000cccc0000c8c80000eecc0000eac80000cccc0000c8c80000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 1264]) (by decide +kernel)

theorem c28652_0 : P.sumLeaves 24 29339648 333 = 11662745 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28652) (lo := 0) (len := 333) (W := 11662745) check rows elimOK (by decide) (by decide) cover28652 (by decide)
  decide +kernel

theorem c28652_1 : P.sumLeaves 24 29339981 155 = 31676116 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28652) (lo := 333) (len := 155) (W := 31676116) check rows elimOK (by decide) (by decide) cover28652 (by decide)
  decide +kernel

theorem c28652_2 : P.sumLeaves 24 29340136 190 = 31514912 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28652) (lo := 488) (len := 190) (W := 31514912) check rows elimOK (by decide) (by decide) cover28652 (by decide)
  decide +kernel

theorem c28652_3 : P.sumLeaves 24 29340326 152 = 39647859 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28652) (lo := 678) (len := 152) (W := 39647859) check rows elimOK (by decide) (by decide) cover28652 (by decide)
  decide +kernel

theorem c28652_4 : P.sumLeaves 24 29340478 124 = 61804939 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28652) (lo := 830) (len := 124) (W := 61804939) check rows elimOK (by decide) (by decide) cover28652 (by decide)
  decide +kernel

theorem c28652_5 : P.sumLeaves 24 29340602 70 = 81854982 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28652) (lo := 954) (len := 70) (W := 81854982) check rows elimOK (by decide) (by decide) cover28652 (by decide)
  decide +kernel

theorem h28652 : P.leaf 34 28652 = 258161553 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(333, 11662745), (155, 31676116), (190, 31514912), (152, 39647859), (124, 61804939), (70, 81854982)]) (.cons c28652_0 (.cons c28652_1 (.cons c28652_2 (.cons c28652_3 (.cons c28652_4 (.cons c28652_5 (.nil))))))) (by decide) (by decide))

theorem cover28653 : P.CoversSplit 24 10 28653 0xffffffffeaeaaaaaffffffffeaeaaaaaffffffffeaeaaaaaffffffffeaeaaaaaffccffcceac8aa88ccccccccc8c88888ffccffcceac8aa88ccccccccc8c88888ffffffffeaeaaaaaffff0000eaea0000ffffffffeaeaaaaaffff0000eaea0000ffcc0000eac80000cccc0000c8c80000ffcc0000eac80000cccc0000c8c80000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 1202, 1259, 1264, 1601]) (by decide +kernel)

theorem c28653_0 : P.sumLeaves 24 29340672 325 = 28646618 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28653) (lo := 0) (len := 325) (W := 28646618) check rows elimOK (by decide) (by decide) cover28653 (by decide)
  decide +kernel

theorem c28653_1 : P.sumLeaves 24 29340997 159 = 55237035 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28653) (lo := 325) (len := 159) (W := 55237035) check rows elimOK (by decide) (by decide) cover28653 (by decide)
  decide +kernel

theorem c28653_2 : P.sumLeaves 24 29341156 175 = 60321869 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28653) (lo := 484) (len := 175) (W := 60321869) check rows elimOK (by decide) (by decide) cover28653 (by decide)
  decide +kernel

theorem c28653_3 : P.sumLeaves 24 29341331 159 = 74683575 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28653) (lo := 659) (len := 159) (W := 74683575) check rows elimOK (by decide) (by decide) cover28653 (by decide)
  decide +kernel

theorem c28653_4 : P.sumLeaves 24 29341490 124 = 85474288 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28653) (lo := 818) (len := 124) (W := 85474288) check rows elimOK (by decide) (by decide) cover28653 (by decide)
  decide +kernel

theorem c28653_5 : P.sumLeaves 24 29341614 82 = 139032772 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28653) (lo := 942) (len := 82) (W := 139032772) check rows elimOK (by decide) (by decide) cover28653 (by decide)
  decide +kernel

theorem h28653 : P.leaf 34 28653 = 443396157 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(325, 28646618), (159, 55237035), (175, 60321869), (159, 74683575), (124, 85474288), (82, 139032772)]) (.cons c28653_0 (.cons c28653_1 (.cons c28653_2 (.cons c28653_3 (.cons c28653_4 (.cons c28653_5 (.nil))))))) (by decide) (by decide))

theorem cover28654 : P.CoversSplit 24 10 28654 0xfffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafaeecceecceac8eac8ccccccccc8c8c8c8eecceecceac8eac8ccccccccc8c8c8c8fffffffffafafafaffff0000fafa0000fffffffffafafafaffff0000fafa0000eecc0000eac80000cccc0000c8c80000eecc0000eac80000cccc0000c8c80000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 522, 1202, 1259, 1264, 1601]) (by decide +kernel)

theorem c28654_0 : P.sumLeaves 24 29341696 326 = 34303892 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28654) (lo := 0) (len := 326) (W := 34303892) check rows elimOK (by decide) (by decide) cover28654 (by decide)
  decide +kernel

theorem c28654_1 : P.sumLeaves 24 29342022 144 = 63999032 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28654) (lo := 326) (len := 144) (W := 63999032) check rows elimOK (by decide) (by decide) cover28654 (by decide)
  decide +kernel

theorem c28654_2 : P.sumLeaves 24 29342166 160 = 68952951 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28654) (lo := 470) (len := 160) (W := 68952951) check rows elimOK (by decide) (by decide) cover28654 (by decide)
  decide +kernel

theorem c28654_3 : P.sumLeaves 24 29342326 170 = 86138171 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28654) (lo := 630) (len := 170) (W := 86138171) check rows elimOK (by decide) (by decide) cover28654 (by decide)
  decide +kernel

theorem c28654_4 : P.sumLeaves 24 29342496 108 = 85419256 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28654) (lo := 800) (len := 108) (W := 85419256) check rows elimOK (by decide) (by decide) cover28654 (by decide)
  decide +kernel

theorem c28654_5 : P.sumLeaves 24 29342604 108 = 181442973 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28654) (lo := 908) (len := 108) (W := 181442973) check rows elimOK (by decide) (by decide) cover28654 (by decide)
  decide +kernel

theorem c28654_6 : P.sumLeaves 24 29342712 8 = 25850632 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28654) (lo := 1016) (len := 8) (W := 25850632) check rows elimOK (by decide) (by decide) cover28654 (by decide)
  decide +kernel

theorem h28654 : P.leaf 34 28654 = 546106907 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(326, 34303892), (144, 63999032), (160, 68952951), (170, 86138171), (108, 85419256), (108, 181442973), (8, 25850632)]) (.cons c28654_0 (.cons c28654_1 (.cons c28654_2 (.cons c28654_3 (.cons c28654_4 (.cons c28654_5 (.cons c28654_6 (.nil)))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(28652, 24), (28653, 24), (28654, 48)]

theorem segOK : checkSeg 16 perms 28652 28655 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 28652 28655 96 43050516576 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 43050516576)
    (SegSum.cons (w := 24) h28652 (SegSum.cons (w := 24) h28653 (SegSum.cons (w := 48) h28654 (show SegSum (P.leaf 34) [] 0 from rfl)))) (by decide)

end RACert.S4N1.C0.S104
