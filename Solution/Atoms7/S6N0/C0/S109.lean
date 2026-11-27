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

namespace RACert.S6N0.C0.S109

open RACert RACert.Problem

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
  leaf_weighted (k := 26) (d := 10) (H := 243695) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 243695) (by decide) (by decide +kernel)) sum243695

theorem cover243699 : P.CoversSplit 26 10 243699 0xfffffffffffffffffffffafafffffafaffffffffffccccccffffaaaaffcc8888ffffffffffffffffffffaaaaffffaaaaffffffffffccccccffffaaaaffcc8888fffffffffffffffffffffafafffffafaffffffffccccccccffffaaaacccc8888ffffffffffffffffffffaaaaffffaaaaffffffffccccccccffffaaaacccc8888 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 1322, 1658]) (by decide +kernel)

noncomputable def f243699 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 26 (249547776 + i)

theorem c243699_0 : rowSum f243699 0 241 = 44190174 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 243699) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover243699 (by decide)
  decide +kernel

theorem c243699_1 : rowSum f243699 241 148 = 244325750 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 243699) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover243699 (by decide)
  decide +kernel

theorem c243699_2 : rowSum f243699 389 102 = 569439786 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 243699) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover243699 (by decide)
  decide +kernel

theorem c243699_3 : rowSum f243699 491 403 = 628929188 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 243699) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover243699 (by decide)
  decide +kernel

theorem c243699_4 : rowSum f243699 894 130 = 473288676 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 243699) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover243699 (by decide)
  decide +kernel

theorem sum243699 : rowSum f243699 0 1024 = 1960173574 :=
  rowSum_append (F := f243699) (lo := 0) (n := 241) (m := 783) (A := 44190174) (B := 1915983400) c243699_0 (rowSum_append (F := f243699) (lo := 241) (n := 148) (m := 635) (A := 244325750) (B := 1671657650) c243699_1 (rowSum_append (F := f243699) (lo := 389) (n := 102) (m := 533) (A := 569439786) (B := 1102217864) c243699_2 (rowSum_append (F := f243699) (lo := 491) (n := 403) (m := 130) (A := 628929188) (B := 473288676) c243699_3 (c243699_4))))

theorem h243699 : P.leaf 36 243699 = 1960173574 :=
  leaf_weighted (k := 26) (d := 10) (H := 243699) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 243699) (by decide) (by decide +kernel)) sum243699

theorem cover243702 : P.CoversSplit 26 10 243702 0xfffffffffffffffffffffffffffffafaffffffffffffccccffffaaaaffcc8888ffffffffffffffffffffa0a0ffffa0a0ffffffffffffccccffffa0a0ffcc8080fffffffffffffffffffffffffffffafaffccffccccccccccffccaa88cccc8888ffffffffffffffffffffa0a0ffffa0a0ffccffccccccccccffcca080cccc8080 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 873, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c243702_0 : P.sumLeaves 26 249550848 183 = 25023523 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243702) (lo := 0) (len := 183) (W := 25023523) check rows elimOK (by decide) (by decide) cover243702 (by decide)
  decide +kernel

theorem c243702_1 : P.sumLeaves 26 249551031 130 = 54113144 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243702) (lo := 183) (len := 130) (W := 54113144) check rows elimOK (by decide) (by decide) cover243702 (by decide)
  decide +kernel

theorem c243702_2 : P.sumLeaves 26 249551161 124 = 171817559 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243702) (lo := 313) (len := 124) (W := 171817559) check rows elimOK (by decide) (by decide) cover243702 (by decide)
  decide +kernel

theorem c243702_3 : P.sumLeaves 26 249551285 126 = 276954103 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243702) (lo := 437) (len := 126) (W := 276954103) check rows elimOK (by decide) (by decide) cover243702 (by decide)
  decide +kernel

theorem c243702_4 : P.sumLeaves 26 249551411 128 = 216805921 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243702) (lo := 563) (len := 128) (W := 216805921) check rows elimOK (by decide) (by decide) cover243702 (by decide)
  decide +kernel

theorem c243702_5 : P.sumLeaves 26 249551539 116 = 305953707 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243702) (lo := 691) (len := 116) (W := 305953707) check rows elimOK (by decide) (by decide) cover243702 (by decide)
  decide +kernel

theorem c243702_6 : P.sumLeaves 26 249551655 112 = 359301952 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243702) (lo := 807) (len := 112) (W := 359301952) check rows elimOK (by decide) (by decide) cover243702 (by decide)
  decide +kernel

theorem c243702_7 : P.sumLeaves 26 249551767 96 = 475918268 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243702) (lo := 919) (len := 96) (W := 475918268) check rows elimOK (by decide) (by decide) cover243702 (by decide)
  decide +kernel

theorem c243702_8 : P.sumLeaves 26 249551863 9 = 104883600 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243702) (lo := 1015) (len := 9) (W := 104883600) check rows elimOK (by decide) (by decide) cover243702 (by decide)
  decide +kernel

theorem h243702 : P.leaf 36 243702 = 1990771777 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(183, 25023523), (130, 54113144), (124, 171817559), (126, 276954103), (128, 216805921), (116, 305953707), (112, 359301952), (96, 475918268), (9, 104883600)]) (.cons c243702_0 (.cons c243702_1 (.cons c243702_2 (.cons c243702_3 (.cons c243702_4 (.cons c243702_5 (.cons c243702_6 (.cons c243702_7 (.cons c243702_8 (.nil)))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(243695, 360), (243699, 120), (243702, 360)]

theorem segOK : checkSeg 20 perms 243695 243703 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 243695 243703 840 3028181232000 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 3028181232000)
    (SegSum.cons (w := 360) h243695 (SegSum.cons (w := 120) h243699 (SegSum.cons (w := 360) h243702 (show SegSum (P.leaf 36) [] 0 from rfl)))) (by decide)

end RACert.S6N0.C0.S109
