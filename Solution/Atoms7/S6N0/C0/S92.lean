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

namespace RACert.S6N0.C0.S92

open RACert RACert.Problem

theorem cover120813 : P.CoversSplit 26 10 120813 0xfffffffffffffafafffffffffffffafaffffffffffffc8c8fafafafac8c8c8c8fffffafafffffafafafaf0f0fafaf0f0fffffafaffffc8c8fafaf0f0c8c8c0c0fffffffffffffafafffffffffffffafaffffffffcc00c800fafafafac800c800fffffafafffffafafafaf0f0fafaf0f0fffffafacc00c800fafaf0f0c800c000 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 922, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c120813_0 : P.sumLeaves 26 123712512 188 = 50005934 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120813) (lo := 0) (len := 188) (W := 50005934) check rows elimOK (by decide) (by decide) cover120813 (by decide)
  decide +kernel

theorem c120813_1 : P.sumLeaves 26 123712700 163 = 69597616 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120813) (lo := 188) (len := 163) (W := 69597616) check rows elimOK (by decide) (by decide) cover120813 (by decide)
  decide +kernel

theorem c120813_2 : P.sumLeaves 26 123712863 102 = 85918452 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120813) (lo := 351) (len := 102) (W := 85918452) check rows elimOK (by decide) (by decide) cover120813 (by decide)
  decide +kernel

theorem c120813_3 : P.sumLeaves 26 123712965 142 = 135053323 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120813) (lo := 453) (len := 142) (W := 135053323) check rows elimOK (by decide) (by decide) cover120813 (by decide)
  decide +kernel

theorem c120813_4 : P.sumLeaves 26 123713107 128 = 148668036 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120813) (lo := 595) (len := 128) (W := 148668036) check rows elimOK (by decide) (by decide) cover120813 (by decide)
  decide +kernel

theorem c120813_5 : P.sumLeaves 26 123713235 138 = 223710009 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120813) (lo := 723) (len := 138) (W := 223710009) check rows elimOK (by decide) (by decide) cover120813 (by decide)
  decide +kernel

theorem c120813_6 : P.sumLeaves 26 123713373 102 = 200101850 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120813) (lo := 861) (len := 102) (W := 200101850) check rows elimOK (by decide) (by decide) cover120813 (by decide)
  decide +kernel

theorem c120813_7 : P.sumLeaves 26 123713475 61 = 249641065 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120813) (lo := 963) (len := 61) (W := 249641065) check rows elimOK (by decide) (by decide) cover120813 (by decide)
  decide +kernel

theorem h120813 : P.leaf 36 120813 = 1162696285 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(188, 50005934), (163, 69597616), (102, 85918452), (142, 135053323), (128, 148668036), (138, 223710009), (102, 200101850), (61, 249641065)]) (.cons c120813_0 (.cons c120813_1 (.cons c120813_2 (.cons c120813_3 (.cons c120813_4 (.cons c120813_5 (.cons c120813_6 (.cons c120813_7 (.nil))))))))) (by decide) (by decide))

theorem cover120815 : P.CoversSplit 26 10 120815 0xfffffffffffffafafffffffffffffafaffffffffffffc8c8fafafafac8c8c8c8fffffafafffffafafafafafafafafafafffffafaffffc8c8fafafafac8c8c8c8fffffffffffffafafffffffffffffafaffffffffcc00c800fafafafac800c800fffffafafffffafafafafafafafafafafffffafacc00c800fafafafac800c800 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c120815_0 : P.sumLeaves 26 123714560 171 = 169004500 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120815) (lo := 0) (len := 171) (W := 169004500) check rows elimOK (by decide) (by decide) cover120815 (by decide)
  decide +kernel

theorem c120815_1 : P.sumLeaves 26 123714731 140 = 230257551 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120815) (lo := 171) (len := 140) (W := 230257551) check rows elimOK (by decide) (by decide) cover120815 (by decide)
  decide +kernel

theorem c120815_2 : P.sumLeaves 26 123714871 127 = 248210434 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120815) (lo := 311) (len := 127) (W := 248210434) check rows elimOK (by decide) (by decide) cover120815 (by decide)
  decide +kernel

theorem c120815_3 : P.sumLeaves 26 123714998 126 = 368005101 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120815) (lo := 438) (len := 126) (W := 368005101) check rows elimOK (by decide) (by decide) cover120815 (by decide)
  decide +kernel

theorem c120815_4 : P.sumLeaves 26 123715124 125 = 353064938 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120815) (lo := 564) (len := 125) (W := 353064938) check rows elimOK (by decide) (by decide) cover120815 (by decide)
  decide +kernel

theorem c120815_5 : P.sumLeaves 26 123715249 133 = 477458566 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120815) (lo := 689) (len := 133) (W := 477458566) check rows elimOK (by decide) (by decide) cover120815 (by decide)
  decide +kernel

theorem c120815_6 : P.sumLeaves 26 123715382 112 = 395124829 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120815) (lo := 822) (len := 112) (W := 395124829) check rows elimOK (by decide) (by decide) cover120815 (by decide)
  decide +kernel

theorem c120815_7 : P.sumLeaves 26 123715494 90 = 530969472 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120815) (lo := 934) (len := 90) (W := 530969472) check rows elimOK (by decide) (by decide) cover120815 (by decide)
  decide +kernel

theorem h120815 : P.leaf 36 120815 = 2772095391 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(171, 169004500), (140, 230257551), (127, 248210434), (126, 368005101), (125, 353064938), (133, 477458566), (112, 395124829), (90, 530969472)]) (.cons c120815_0 (.cons c120815_1 (.cons c120815_2 (.cons c120815_3 (.cons c120815_4 (.cons c120815_5 (.cons c120815_6 (.cons c120815_7 (.nil))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(120813, 720), (120815, 360)]

theorem segOK : checkSeg 20 perms 120813 120819 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 120813 120819 1080 1835095665960 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1835095665960)
    (SegSum.cons (w := 720) h120813 (SegSum.cons (w := 360) h120815 (show SegSum (P.leaf 36) [] 0 from rfl))) (by decide)

end RACert.S6N0.C0.S92
