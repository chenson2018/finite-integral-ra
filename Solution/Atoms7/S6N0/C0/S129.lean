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

namespace RACert.S6N0.C0.S129

open RACert RACert.Problem

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

theorem cover243703 : P.CoversSplit 26 10 243703 0xfffffffffffffffffffffffffffffafaffffffffffffccccffffaaaaffcc8888ffffffffffffffffffffaaaaffffaaaaffffffffffffccccffffaaaaffcc8888fffffffffffffffffffffffffffffafaffffffffccccccccffffaaaacccc8888ffffffffffffffffffffaaaaffffaaaaffffffffccccccccffffaaaacccc8888 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 873, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c243703_0 : P.sumLeaves 26 249551872 148 = 88965087 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243703) (lo := 0) (len := 148) (W := 88965087) check rows elimOK (by decide) (by decide) cover243703 (by decide)
  decide +kernel

theorem c243703_1 : P.sumLeaves 26 249552020 104 = 136612981 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243703) (lo := 148) (len := 104) (W := 136612981) check rows elimOK (by decide) (by decide) cover243703 (by decide)
  decide +kernel

theorem c243703_2 : P.sumLeaves 26 249552124 144 = 447800385 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243703) (lo := 252) (len := 144) (W := 447800385) check rows elimOK (by decide) (by decide) cover243703 (by decide)
  decide +kernel

theorem c243703_3 : P.sumLeaves 26 249552268 96 = 628491103 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243703) (lo := 396) (len := 96) (W := 628491103) check rows elimOK (by decide) (by decide) cover243703 (by decide)
  decide +kernel

theorem c243703_4 : P.sumLeaves 26 249552364 128 = 499557648 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243703) (lo := 492) (len := 128) (W := 499557648) check rows elimOK (by decide) (by decide) cover243703 (by decide)
  decide +kernel

theorem c243703_5 : P.sumLeaves 26 249552492 112 = 422294776 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243703) (lo := 620) (len := 112) (W := 422294776) check rows elimOK (by decide) (by decide) cover243703 (by decide)
  decide +kernel

theorem c243703_6 : P.sumLeaves 26 249552604 128 = 630296535 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243703) (lo := 732) (len := 128) (W := 630296535) check rows elimOK (by decide) (by decide) cover243703 (by decide)
  decide +kernel

theorem c243703_7 : P.sumLeaves 26 249552732 100 = 783672649 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243703) (lo := 860) (len := 100) (W := 783672649) check rows elimOK (by decide) (by decide) cover243703 (by decide)
  decide +kernel

theorem c243703_8 : P.sumLeaves 26 249552832 64 = 631887940 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243703) (lo := 960) (len := 64) (W := 631887940) check rows elimOK (by decide) (by decide) cover243703 (by decide)
  decide +kernel

theorem h243703 : P.leaf 36 243703 = 4269579104 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(148, 88965087), (104, 136612981), (144, 447800385), (96, 628491103), (128, 499557648), (112, 422294776), (128, 630296535), (100, 783672649), (64, 631887940)]) (.cons c243703_0 (.cons c243703_1 (.cons c243703_2 (.cons c243703_3 (.cons c243703_4 (.cons c243703_5 (.cons c243703_6 (.cons c243703_7 (.cons c243703_8 (.nil)))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(243702, 360), (243703, 720)]

theorem segOK : checkSeg 20 perms 243702 243708 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 243702 243708 1080 3790774794600 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 3790774794600)
    (SegSum.cons (w := 360) h243702 (SegSum.cons (w := 720) h243703 (show SegSum (P.leaf 36) [] 0 from rfl))) (by decide)

end RACert.S6N0.C0.S129
