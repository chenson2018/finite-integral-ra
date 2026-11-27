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

namespace RACert.S6N0.C0.S37

open RACert RACert.Problem

theorem cover31729 : P.CoversSplit 26 10 31729 0xf000f000f000f000f000a000f000a000f000f000c000c000f000a000c000800800000000000000000000aa000000aa0000000000000000000000aa00000088080000000000000000000000000000000000000000c0c0c0c000000000c0c080880000000000000000000000000000000000000000000000000000000000008888 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 972, 979, 1265, 1273]) (by decide +kernel)

theorem c31729_0 : P.sumLeaves 26 32490496 1024 = 8014232 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31729) (lo := 0) (len := 1024) (W := 8014232) check rows elimOK (by decide) (by decide) cover31729 (by decide)
  decide +kernel

theorem h31729 : P.leaf 36 31729 = 8014232 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8014232)]) (.cons c31729_0 (.nil)) (by decide) (by decide))

theorem cover31731 : P.CoversSplit 26 10 31731 0xf000f000f000f000f000a000f000a000f000f000c000c000f000a000c000800800000000000000000000aa000000aa0000000000000000000000aa00000088080000000000000000000000000000000000000000c0c0c0c000000000c0c080880000000000000000000000000000000000000000000000000000000000008888 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 972, 979, 1265, 1273]) (by decide +kernel)

theorem c31731_0 : P.sumLeaves 26 32492544 1024 = 65602384 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31731) (lo := 0) (len := 1024) (W := 65602384) check rows elimOK (by decide) (by decide) cover31731 (by decide)
  decide +kernel

theorem h31731 : P.leaf 36 31731 = 65602384 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 65602384)]) (.cons c31731_0 (.nil)) (by decide) (by decide))

theorem cover31733 : P.CoversSplit 26 10 31733 0xff00ff00ff00fa00ff00aa00ff00aa00ff00ff00cc00c800fa00aa00c8008800ff00fa00ff00fa00fa00a000fa00a000ff00fa00cc00c800fa00a000c800800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 929, 972, 979, 1265, 1273, 1315, 1658]) (by decide +kernel)

theorem c31733_0 : P.sumLeaves 26 32494592 859 = 30721768 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31733) (lo := 0) (len := 859) (W := 30721768) check rows elimOK (by decide) (by decide) cover31733 (by decide)
  decide +kernel

theorem c31733_1 : P.sumLeaves 26 32495451 165 = 52474432 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31733) (lo := 859) (len := 165) (W := 52474432) check rows elimOK (by decide) (by decide) cover31733 (by decide)
  decide +kernel

theorem h31733 : P.leaf 36 31733 = 83196200 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(859, 30721768), (165, 52474432)]) (.cons c31733_0 (.cons c31733_1 (.nil))) (by decide) (by decide))

theorem cover31735 : P.CoversSplit 26 10 31735 0xff00ff00ff00fa00ff00aa00ff00aa00ff00ff00cc00c800fa00aa00c8008800ff00fa00ff00fa00fa00a000fa00a000ff00fa00cc00c800fa00a000c800800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 972, 979, 1265, 1273, 1315, 1658]) (by decide +kernel)

theorem c31735_0 : P.sumLeaves 26 32496640 859 = 160213276 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31735) (lo := 0) (len := 859) (W := 160213276) check rows elimOK (by decide) (by decide) cover31735 (by decide)
  decide +kernel

theorem c31735_1 : P.sumLeaves 26 32497499 165 = 265957820 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31735) (lo := 859) (len := 165) (W := 265957820) check rows elimOK (by decide) (by decide) cover31735 (by decide)
  decide +kernel

theorem h31735 : P.leaf 36 31735 = 426171096 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(859, 160213276), (165, 265957820)]) (.cons c31735_0 (.cons c31735_1 (.nil))) (by decide) (by decide))

theorem cover31743 : P.CoversSplit 26 10 31743 0xfffffffffffffac8ffffaaaaffffaa88ffffffffccccc8c8fac8aa88c8c88888fffffafafffffac8fafaaaaafafaaa88fffffafaccccc8c8fac8aa88c8c88888ffffffffffccfac8ffffaaaaffccaa88ffccffccccccc8c8fac8aa88c8c88888fffffafaffccfac8fafaaaaafac8aa88ffccfac8ccccc8c8fac8aa88c8c88888 :=
  coversSplit check rows (by decide) (by decide) (xs := [972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c31743_0 : P.sumLeaves 26 32504832 198 = 8421664 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31743) (lo := 0) (len := 198) (W := 8421664) check rows elimOK (by decide) (by decide) cover31743 (by decide)
  decide +kernel

theorem c31743_1 : P.sumLeaves 26 32505030 167 = 189891615 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31743) (lo := 198) (len := 167) (W := 189891615) check rows elimOK (by decide) (by decide) cover31743 (by decide)
  decide +kernel

theorem c31743_2 : P.sumLeaves 26 32505197 133 = 381994483 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31743) (lo := 365) (len := 133) (W := 381994483) check rows elimOK (by decide) (by decide) cover31743 (by decide)
  decide +kernel

theorem c31743_3 : P.sumLeaves 26 32505330 171 = 400791044 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31743) (lo := 498) (len := 171) (W := 400791044) check rows elimOK (by decide) (by decide) cover31743 (by decide)
  decide +kernel

theorem c31743_4 : P.sumLeaves 26 32505501 158 = 463641442 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31743) (lo := 669) (len := 158) (W := 463641442) check rows elimOK (by decide) (by decide) cover31743 (by decide)
  decide +kernel

theorem c31743_5 : P.sumLeaves 26 32505659 132 = 635544684 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31743) (lo := 827) (len := 132) (W := 635544684) check rows elimOK (by decide) (by decide) cover31743 (by decide)
  decide +kernel

theorem c31743_6 : P.sumLeaves 26 32505791 65 = 495760088 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31743) (lo := 959) (len := 65) (W := 495760088) check rows elimOK (by decide) (by decide) cover31743 (by decide)
  decide +kernel

theorem h31743 : P.leaf 36 31743 = 2576045020 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(198, 8421664), (167, 189891615), (133, 381994483), (171, 400791044), (158, 463641442), (132, 635544684), (65, 495760088)]) (.cons c31743_0 (.cons c31743_1 (.cons c31743_2 (.cons c31743_3 (.cons c31743_4 (.cons c31743_5 (.cons c31743_6 (.nil)))))))) (by decide) (by decide))

theorem cover32243 : P.CoversSplit 26 10 32243 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c32243_0 : P.sumLeaves 26 33016832 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32243) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover32243 (by decide)
  decide +kernel

theorem h32243 : P.leaf 36 32243 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c32243_0 (.nil)) (by decide) (by decide))

theorem cover32244 : P.CoversSplit 26 10 32244 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c32244_0 : P.sumLeaves 26 33017856 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32244) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover32244 (by decide)
  decide +kernel

theorem h32244 : P.leaf 36 32244 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c32244_0 (.nil)) (by decide) (by decide))

theorem cover32245 : P.CoversSplit 26 10 32245 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c32245_0 : P.sumLeaves 26 33018880 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32245) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover32245 (by decide)
  decide +kernel

theorem h32245 : P.leaf 36 32245 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c32245_0 (.nil)) (by decide) (by decide))

theorem cover32247 : P.CoversSplit 26 10 32247 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c32247_0 : P.sumLeaves 26 33020928 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32247) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover32247 (by decide)
  decide +kernel

theorem h32247 : P.leaf 36 32247 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c32247_0 (.nil)) (by decide) (by decide))

theorem cover32252 : P.CoversSplit 26 10 32252 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c32252_0 : P.sumLeaves 26 33026048 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32252) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover32252 (by decide)
  decide +kernel

theorem h32252 : P.leaf 36 32252 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c32252_0 (.nil)) (by decide) (by decide))

theorem cover32253 : P.CoversSplit 26 10 32253 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c32253_0 : P.sumLeaves 26 33027072 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32253) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover32253 (by decide)
  decide +kernel

theorem h32253 : P.leaf 36 32253 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c32253_0 (.nil)) (by decide) (by decide))

theorem cover32255 : P.CoversSplit 26 10 32255 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c32255_0 : P.sumLeaves 26 33029120 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32255) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover32255 (by decide)
  decide +kernel

theorem h32255 : P.leaf 36 32255 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c32255_0 (.nil)) (by decide) (by decide))

theorem cover32496 : P.CoversSplit 26 10 32496 0xc000c000c000c000c000c000c000c0000000000000000000000000000000000000000000000000000000c0000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 587, 972, 979, 1658, 1665]) (by decide +kernel)

theorem c32496_0 : P.sumLeaves 26 33275904 1024 = 134080 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32496) (lo := 0) (len := 1024) (W := 134080) check rows elimOK (by decide) (by decide) cover32496 (by decide)
  decide +kernel

theorem h32496 : P.leaf 36 32496 = 134080 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 134080)]) (.cons c32496_0 (.nil)) (by decide) (by decide))

theorem cover32497 : P.CoversSplit 26 10 32497 0xc000c000c000c000c000c000c000c0000000000000000000000000000000000000000000000000000000c0000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 587, 972, 979, 1658, 1665]) (by decide +kernel)

theorem c32497_0 : P.sumLeaves 26 33276928 1024 = 4254080 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32497) (lo := 0) (len := 1024) (W := 4254080) check rows elimOK (by decide) (by decide) cover32497 (by decide)
  decide +kernel

theorem h32497 : P.leaf 36 32497 = 4254080 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4254080)]) (.cons c32497_0 (.nil)) (by decide) (by decide))

theorem cover32498 : P.CoversSplit 26 10 32498 0xc000c000c000c000c000c000c000c0000000000000000000000000000000000000000000000000000000c0000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 587, 972, 979, 1658, 1665]) (by decide +kernel)

theorem c32498_0 : P.sumLeaves 26 33277952 1024 = 9554000 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32498) (lo := 0) (len := 1024) (W := 9554000) check rows elimOK (by decide) (by decide) cover32498 (by decide)
  decide +kernel

theorem h32498 : P.leaf 36 32498 = 9554000 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 9554000)]) (.cons c32498_0 (.nil)) (by decide) (by decide))

theorem cover32499 : P.CoversSplit 26 10 32499 0xc000c000c000c000c000c000c000c0000000000000000000000000000000000000000000000000000000c0000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 587, 972, 979, 1658, 1665]) (by decide +kernel)

theorem c32499_0 : P.sumLeaves 26 33278976 1024 = 23784464 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32499) (lo := 0) (len := 1024) (W := 23784464) check rows elimOK (by decide) (by decide) cover32499 (by decide)
  decide +kernel

theorem h32499 : P.leaf 36 32499 = 23784464 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 23784464)]) (.cons c32499_0 (.nil)) (by decide) (by decide))

theorem cover32502 : P.CoversSplit 26 10 32502 0xcc00cc00cc00c800cc00c800cc00c80000000000000000000000000000000000cc00c800cc00c800c000c000c000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 587, 880, 972, 979, 1265, 1315, 1658]) (by decide +kernel)

theorem c32502_0 : P.sumLeaves 26 33282048 1024 = 61133808 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32502) (lo := 0) (len := 1024) (W := 61133808) check rows elimOK (by decide) (by decide) cover32502 (by decide)
  decide +kernel

theorem h32502 : P.leaf 36 32502 = 61133808 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 61133808)]) (.cons c32502_0 (.nil)) (by decide) (by decide))

theorem cover32503 : P.CoversSplit 26 10 32503 0xcc00cc00cc00c800cc00c800cc00c80000000000000000000000000000000000cc00c800cc00c800c000c000c000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 587, 972, 979, 1265, 1315, 1658]) (by decide +kernel)

theorem c32503_0 : P.sumLeaves 26 33283072 1024 = 124748000 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32503) (lo := 0) (len := 1024) (W := 124748000) check rows elimOK (by decide) (by decide) cover32503 (by decide)
  decide +kernel

theorem h32503 : P.leaf 36 32503 = 124748000 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 124748000)]) (.cons c32503_0 (.nil)) (by decide) (by decide))

theorem cover32504 : P.CoversSplit 26 10 32504 0xf0f0f0f0f0f0f0c0f0f0f0f0f0f0f0c000000000000000000030003000000000000000000000000000005050000050400000000000000000000000100000000000300030000000000030003000000000003000300000000000300030000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 587, 874, 972, 979, 1265, 1273, 1322, 1665]) (by decide +kernel)

theorem c32504_0 : P.sumLeaves 26 33284096 1024 = 7238172 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32504) (lo := 0) (len := 1024) (W := 7238172) check rows elimOK (by decide) (by decide) cover32504 (by decide)
  decide +kernel

theorem h32504 : P.leaf 36 32504 = 7238172 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 7238172)]) (.cons c32504_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(31729, 360), (31731, 180), (31733, 360), (31735, 360), (31743, 90), (32243, 45), (32244, 180), (32245, 360), (32247, 180), (32252, 90), (32253, 180), (32255, 90), (32496, 360), (32497, 360), (32498, 720), (32499, 720), (32502, 360), (32503, 360), (32504, 360)]

theorem segOK : checkSeg 20 perms 31729 32505 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 31729 32505 5715 525016455480 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 525016455480)
    (SegSum.cons (w := 360) h31729 (SegSum.cons (w := 180) h31731 (SegSum.cons (w := 360) h31733 (SegSum.cons (w := 360) h31735 (SegSum.cons (w := 90) h31743 (SegSum.cons (w := 45) h32243 (SegSum.cons (w := 180) h32244 (SegSum.cons (w := 360) h32245 (SegSum.cons (w := 180) h32247 (SegSum.cons (w := 90) h32252 (SegSum.cons (w := 180) h32253 (SegSum.cons (w := 90) h32255 (SegSum.cons (w := 360) h32496 (SegSum.cons (w := 360) h32497 (SegSum.cons (w := 720) h32498 (SegSum.cons (w := 720) h32499 (SegSum.cons (w := 360) h32502 (SegSum.cons (w := 360) h32503 (SegSum.cons (w := 360) h32504 (show SegSum (P.leaf 36) [] 0 from rfl)))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S37
