/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S6N0.C0.Actions

/-! Generated identity-class certificate for the product-row count. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S6N0.C0.S91

open RACert RACert.Problem

theorem cover802782 : P.CoversSplit 26 10 802782 0xfffffffafffffffafffffafafffffafaffff0000ffcc0000ffff0000ffcc0000fffffafafffffafaffffaaaaffffaaaaffff0000ffcc0000ffff0000ffcc0000fffffffafffffffafffffafafffffafaffff0000ffcc0000ffff0000ffcc0000fffffafafffffafaffffaaaaffffaaaaffff0000ffcc0000ffff0000ffcc0000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 930, 972, 979, 1265, 1272, 1273]) (by decide +kernel)

theorem c802782_0 : P.sumLeaves 26 822048768 184 = 145838369 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 802782) (lo := 0) (len := 184) (W := 145838369) check rows elimOK (by decide) (by decide) cover802782 (by decide)
  decide +kernel

theorem c802782_1 : P.sumLeaves 26 822048952 160 = 268967802 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 802782) (lo := 184) (len := 160) (W := 268967802) check rows elimOK (by decide) (by decide) cover802782 (by decide)
  decide +kernel

theorem c802782_2 : P.sumLeaves 26 822049112 122 = 369874040 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 802782) (lo := 344) (len := 122) (W := 369874040) check rows elimOK (by decide) (by decide) cover802782 (by decide)
  decide +kernel

theorem c802782_3 : P.sumLeaves 26 822049234 170 = 407231761 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 802782) (lo := 466) (len := 170) (W := 407231761) check rows elimOK (by decide) (by decide) cover802782 (by decide)
  decide +kernel

theorem c802782_4 : P.sumLeaves 26 822049404 120 = 381625036 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 802782) (lo := 636) (len := 120) (W := 381625036) check rows elimOK (by decide) (by decide) cover802782 (by decide)
  decide +kernel

theorem c802782_5 : P.sumLeaves 26 822049524 173 = 433896925 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 802782) (lo := 756) (len := 173) (W := 433896925) check rows elimOK (by decide) (by decide) cover802782 (by decide)
  decide +kernel

theorem c802782_6 : P.sumLeaves 26 822049697 95 = 524820942 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 802782) (lo := 929) (len := 95) (W := 524820942) check rows elimOK (by decide) (by decide) cover802782 (by decide)
  decide +kernel

theorem h802782 : P.leaf 36 802782 = 2532254875 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(184, 145838369), (160, 268967802), (122, 369874040), (170, 407231761), (120, 381625036), (173, 433896925), (95, 524820942)]) (.cons c802782_0 (.cons c802782_1 (.cons c802782_2 (.cons c802782_3 (.cons c802782_4 (.cons c802782_5 (.cons c802782_6 (.nil)))))))) (by decide) (by decide))

theorem h243693 : P.leaf 36 243693 = 2532254875 :=
  orient86 (v := 802782) (by decide) (by decide +kernel) h802782

theorem cover243695 : P.CoversSplit 26 10 243695 0xfffffffffffffffffffffffffffffafaffffffffffffccccffffaaaaffcc8888ffffffffffffffffffffaaaaffffaaaaffffffffffffccccffffaaaaffcc8888fffffffffffffffffffffffffffffafaffffffffccccccccffffaaaacccc8888ffffffffffffffffffffaaaaffffaaaaffffffffccccccccffffaaaacccc8888 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f243695 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 26 (249543680 + i)

theorem c243695_0 : rowSum f243695 0 241 = 536078787 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 243695) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover243695 (by decide)
  decide +kernel

theorem c243695_1 : rowSum f243695 241 148 = 775641176 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 243695) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover243695 (by decide)
  decide +kernel

theorem c243695_2 : rowSum f243695 389 98 = 1601628424 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 243695) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover243695 (by decide)
  decide +kernel

theorem c243695_3 : rowSum f243695 487 399 = 1442656574 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 243695) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover243695 (by decide)
  decide +kernel

theorem c243695_4 : rowSum f243695 886 138 = 1411446604 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 243695) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover243695 (by decide)
  decide +kernel

theorem sum243695 : rowSum f243695 0 1024 = 5767451565 :=
  rowSum_append (F := f243695) (lo := 0) (n := 241) (m := 783) (A := 536078787) (B := 5231372778) c243695_0 (rowSum_append (F := f243695) (lo := 241) (n := 148) (m := 635) (A := 775641176) (B := 4455731602) c243695_1 (rowSum_append (F := f243695) (lo := 389) (n := 98) (m := 537) (A := 1601628424) (B := 2854103178) c243695_2 (rowSum_append (F := f243695) (lo := 487) (n := 399) (m := 138) (A := 1442656574) (B := 1411446604) c243695_3 (c243695_4))))

theorem h243695 : P.leaf 36 243695 = 5767451565 :=
  leaf_weighted (k := 26) (d := 10) (H := 243695) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 243695) (by decide) (by decide +kernel)) sum243695

theorem cover359413 : P.CoversSplit 26 10 359413 0xfffffffffffffffffffffff0fffffff0fffffffffffcfffcfafafaf0fac8fac0fffffffffffffffffafaf0f0fafaf0f0fffffffffffcfffcfafaf0f0fac8f0c0ffffffffffccffccfffffff0ffccffc0ffffffffccccccccfafafaf0c8c8c8c00000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 923, 972, 979, 1273, 1658, 1665]) (by decide +kernel)

noncomputable def f359413 (i : ℕ) := rowWeight keep13 twice13 i * P.leaf 26 (368038912 + i)

theorem c359413_0 : rowSum f359413 0 494 = 501672217 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 359413) (keep := keep13) (twice := twice13) check rows elimOK (by decide) (by decide) cover359413 (by decide)
  decide +kernel

theorem c359413_1 : rowSum f359413 494 208 = 450440052 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 359413) (keep := keep13) (twice := twice13) check rows elimOK (by decide) (by decide) cover359413 (by decide)
  decide +kernel

theorem c359413_2 : rowSum f359413 702 206 = 608923363 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 359413) (keep := keep13) (twice := twice13) check rows elimOK (by decide) (by decide) cover359413 (by decide)
  decide +kernel

theorem c359413_3 : rowSum f359413 908 116 = 399137942 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 359413) (keep := keep13) (twice := twice13) check rows elimOK (by decide) (by decide) cover359413 (by decide)
  decide +kernel

theorem sum359413 : rowSum f359413 0 1024 = 1960173574 :=
  rowSum_append (F := f359413) (lo := 0) (n := 494) (m := 530) (A := 501672217) (B := 1458501357) c359413_0 (rowSum_append (F := f359413) (lo := 494) (n := 208) (m := 322) (A := 450440052) (B := 1008061305) c359413_1 (rowSum_append (F := f359413) (lo := 702) (n := 206) (m := 116) (A := 608923363) (B := 399137942) c359413_2 (c359413_3)))

theorem h359413 : P.leaf 36 359413 = 1960173574 :=
  leaf_weighted (k := 26) (d := 10) (H := 359413) (keep := keep13) (twice := twice13) rows (by decide) (by decide) (bal13) (invRow13 (H := 359413) (by decide) (by decide +kernel)) sum359413

theorem h243699 : P.leaf 36 243699 = 1960173574 :=
  orient4 (v := 359413) (by decide) (by decide +kernel) h359413

def seg : List (ℕ × ℕ) := [(243693, 720), (243695, 360), (243699, 120)]

theorem segOK : checkSeg 20 perms 243693 243702 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 243693 243702 1200 4134726902280 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 4134726902280)
    (SegSum.cons (w := 720) h243693 (SegSum.cons (w := 360) h243695 (SegSum.cons (w := 120) h243699 (show SegSum (P.leaf 36) [] 0 from rfl)))) (by decide)

end RACert.S6N0.C0.S91
