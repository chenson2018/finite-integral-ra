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

namespace RACert.S6N0.C0.S108

open RACert RACert.Problem

theorem cover243683 : P.CoversSplit 26 10 243683 0xfffffffffffffffffffffafafffffafaffffffffffccccccffffaaaaffcc8888ffffffffffffffffffffaaaaffffaaaaffffffffffccccccffffaaaaffcc8888fffffffffffffffffffffafafffffafaffffffffccccccccffffaaaacccc8888ffffffffffffffffffffaaaaffffaaaaffffffffccccccccffffaaaacccc8888 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 1322, 1658]) (by decide +kernel)

noncomputable def f243683 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 26 (249531392 + i)

theorem c243683_0 : rowSum f243683 0 241 = 28400912 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 243683) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover243683 (by decide)
  decide +kernel

theorem c243683_1 : rowSum f243683 241 148 = 137780612 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 243683) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover243683 (by decide)
  decide +kernel

theorem c243683_2 : rowSum f243683 389 102 = 399863084 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 243683) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover243683 (by decide)
  decide +kernel

theorem c243683_3 : rowSum f243683 491 403 = 387689428 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 243683) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover243683 (by decide)
  decide +kernel

theorem c243683_4 : rowSum f243683 894 130 = 388522952 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 243683) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover243683 (by decide)
  decide +kernel

theorem sum243683 : rowSum f243683 0 1024 = 1342256988 :=
  rowSum_append (F := f243683) (lo := 0) (n := 241) (m := 783) (A := 28400912) (B := 1313856076) c243683_0 (rowSum_append (F := f243683) (lo := 241) (n := 148) (m := 635) (A := 137780612) (B := 1176075464) c243683_1 (rowSum_append (F := f243683) (lo := 389) (n := 102) (m := 533) (A := 399863084) (B := 776212380) c243683_2 (rowSum_append (F := f243683) (lo := 491) (n := 403) (m := 130) (A := 387689428) (B := 388522952) c243683_3 (c243683_4))))

theorem h243683 : P.leaf 36 243683 = 1342256988 :=
  leaf_weighted (k := 26) (d := 10) (H := 243683) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 243683) (by decide) (by decide +kernel)) sum243683

theorem cover243687 : P.CoversSplit 26 10 243687 0xfffffffffffffffffffffffffffffafaffffffffffffccccffffaaaaffcc8888ffffffffffffffffffffaaaaffffaaaaffffffffffffccccffffaaaaffcc8888fffffffffffffffffffffffffffffafaffffffffccccccccffffaaaacccc8888ffffffffffffffffffffaaaaffffaaaaffffffffccccccccffffaaaacccc8888 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 873, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c243687_0 : P.sumLeaves 26 249535488 148 = 39188882 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243687) (lo := 0) (len := 148) (W := 39188882) check rows elimOK (by decide) (by decide) cover243687 (by decide)
  decide +kernel

theorem c243687_1 : P.sumLeaves 26 249535636 104 = 102867951 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243687) (lo := 148) (len := 104) (W := 102867951) check rows elimOK (by decide) (by decide) cover243687 (by decide)
  decide +kernel

theorem c243687_2 : P.sumLeaves 26 249535740 144 = 208283738 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243687) (lo := 252) (len := 144) (W := 208283738) check rows elimOK (by decide) (by decide) cover243687 (by decide)
  decide +kernel

theorem c243687_3 : P.sumLeaves 26 249535884 96 = 483826217 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243687) (lo := 396) (len := 96) (W := 483826217) check rows elimOK (by decide) (by decide) cover243687 (by decide)
  decide +kernel

theorem c243687_4 : P.sumLeaves 26 249535980 128 = 310350696 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243687) (lo := 492) (len := 128) (W := 310350696) check rows elimOK (by decide) (by decide) cover243687 (by decide)
  decide +kernel

theorem c243687_5 : P.sumLeaves 26 249536108 112 = 291609345 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243687) (lo := 620) (len := 112) (W := 291609345) check rows elimOK (by decide) (by decide) cover243687 (by decide)
  decide +kernel

theorem c243687_6 : P.sumLeaves 26 249536220 128 = 362976533 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243687) (lo := 732) (len := 128) (W := 362976533) check rows elimOK (by decide) (by decide) cover243687 (by decide)
  decide +kernel

theorem c243687_7 : P.sumLeaves 26 249536348 100 = 555515069 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243687) (lo := 860) (len := 100) (W := 555515069) check rows elimOK (by decide) (by decide) cover243687 (by decide)
  decide +kernel

theorem c243687_8 : P.sumLeaves 26 249536448 64 = 517209676 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243687) (lo := 960) (len := 64) (W := 517209676) check rows elimOK (by decide) (by decide) cover243687 (by decide)
  decide +kernel

theorem h243687 : P.leaf 36 243687 = 2871828107 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(148, 39188882), (104, 102867951), (144, 208283738), (96, 483826217), (128, 310350696), (112, 291609345), (128, 362976533), (100, 555515069), (64, 517209676)]) (.cons c243687_0 (.cons c243687_1 (.cons c243687_2 (.cons c243687_3 (.cons c243687_4 (.cons c243687_5 (.cons c243687_6 (.cons c243687_7 (.cons c243687_8 (.nil)))))))))) (by decide) (by decide))

theorem cover243693 : P.CoversSplit 26 10 243693 0xfffffffffffffffffffffffffffffafaffffffffffffccccffffaaaaffcc8888ffffffffffffffffffffaaaaffffaaaaffffffffffffccccffffaaaaffcc8888fffffffffffffffffffffffffffffafaffffffffcc00cc00ffffaaaacc008800ffffffffffffffffffffaaaaffffaaaaffffffffcc00cc00ffffaaaacc008800 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c243693_0 : P.sumLeaves 26 249541632 165 = 61489277 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243693) (lo := 0) (len := 165) (W := 61489277) check rows elimOK (by decide) (by decide) cover243693 (by decide)
  decide +kernel

theorem c243693_1 : P.sumLeaves 26 249541797 132 = 105731710 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243693) (lo := 165) (len := 132) (W := 105731710) check rows elimOK (by decide) (by decide) cover243693 (by decide)
  decide +kernel

theorem c243693_2 : P.sumLeaves 26 249541929 127 = 224661684 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243693) (lo := 297) (len := 127) (W := 224661684) check rows elimOK (by decide) (by decide) cover243693 (by decide)
  decide +kernel

theorem c243693_3 : P.sumLeaves 26 249542056 112 = 465533406 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243693) (lo := 424) (len := 112) (W := 465533406) check rows elimOK (by decide) (by decide) cover243693 (by decide)
  decide +kernel

theorem c243693_4 : P.sumLeaves 26 249542168 120 = 148388485 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243693) (lo := 536) (len := 120) (W := 148388485) check rows elimOK (by decide) (by decide) cover243693 (by decide)
  decide +kernel

theorem c243693_5 : P.sumLeaves 26 249542288 104 = 280447914 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243693) (lo := 656) (len := 104) (W := 280447914) check rows elimOK (by decide) (by decide) cover243693 (by decide)
  decide +kernel

theorem c243693_6 : P.sumLeaves 26 249542392 128 = 336860575 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243693) (lo := 760) (len := 128) (W := 336860575) check rows elimOK (by decide) (by decide) cover243693 (by decide)
  decide +kernel

theorem c243693_7 : P.sumLeaves 26 249542520 100 = 568276248 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243693) (lo := 888) (len := 100) (W := 568276248) check rows elimOK (by decide) (by decide) cover243693 (by decide)
  decide +kernel

theorem c243693_8 : P.sumLeaves 26 249542620 36 = 340865576 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243693) (lo := 988) (len := 36) (W := 340865576) check rows elimOK (by decide) (by decide) cover243693 (by decide)
  decide +kernel

theorem h243693 : P.leaf 36 243693 = 2532254875 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(165, 61489277), (132, 105731710), (127, 224661684), (112, 465533406), (120, 148388485), (104, 280447914), (128, 336860575), (100, 568276248), (36, 340865576)]) (.cons c243693_0 (.cons c243693_1 (.cons c243693_2 (.cons c243693_3 (.cons c243693_4 (.cons c243693_5 (.cons c243693_6 (.cons c243693_7 (.cons c243693_8 (.nil)))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(243683, 120), (243687, 720), (243693, 720)]

theorem segOK : checkSeg 20 perms 243683 243695 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 243683 243695 1560 4052010585600 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 4052010585600)
    (SegSum.cons (w := 120) h243683 (SegSum.cons (w := 720) h243687 (SegSum.cons (w := 720) h243693 (show SegSum (P.leaf 36) [] 0 from rfl)))) (by decide)

end RACert.S6N0.C0.S108
