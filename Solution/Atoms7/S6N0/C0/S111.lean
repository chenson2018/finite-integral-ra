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

namespace RACert.S6N0.C0.S111

open RACert RACert.Problem

theorem cover229069 : P.CoversSplit 26 10 229069 0xffff0000ffff0000ffff0000ffff050000000000000000000000000000300000000000000000000005050000050500000000000000000000000000000000000000000000003300000000000000330000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 587, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c229069_0 : P.sumLeaves 26 234566656 1024 = 71185308 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229069) (lo := 0) (len := 1024) (W := 71185308) check rows elimOK (by decide) (by decide) cover229069 (by decide)
  decide +kernel

theorem h229069 : P.leaf 36 229069 = 71185308 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 71185308)]) (.cons c229069_0 (.nil)) (by decide) (by decide))

theorem cover229071 : P.CoversSplit 26 10 229071 0xffff0000ffff0000ffff0000ffff050000000000000000000000000000300000000000000000000005050000050500000000000000000000000000000000000000000000003300000000000000330000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 587, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c229071_0 : P.sumLeaves 26 234568704 1024 = 599428428 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229071) (lo := 0) (len := 1024) (W := 599428428) check rows elimOK (by decide) (by decide) cover229071 (by decide)
  decide +kernel

theorem h229071 : P.leaf 36 229071 = 599428428 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 599428428)]) (.cons c229071_0 (.nil)) (by decide) (by decide))

theorem cover229084 : P.CoversSplit 26 10 229084 0xffff0000ffff0000ffff0000ffff050000000000000000000000000000300000000000000000000005050000050500000000000000000000000000000000000000000000003300000000000000330000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 587, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c229084_0 : P.sumLeaves 26 234582016 1024 = 404902368 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229084) (lo := 0) (len := 1024) (W := 404902368) check rows elimOK (by decide) (by decide) cover229084 (by decide)
  decide +kernel

theorem h229084 : P.leaf 36 229084 = 404902368 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 404902368)]) (.cons c229084_0 (.nil)) (by decide) (by decide))

theorem cover229085 : P.CoversSplit 26 10 229085 0xffff0000ffff0000ffff0000ffff050000000000000000000000000000300000000000000000000005050000050500000000000000000000000000000000000000000000003300000000000000330000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 587, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c229085_0 : P.sumLeaves 26 234583040 1024 = 695033356 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229085) (lo := 0) (len := 1024) (W := 695033356) check rows elimOK (by decide) (by decide) cover229085 (by decide)
  decide +kernel

theorem h229085 : P.leaf 36 229085 = 695033356 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 695033356)]) (.cons c229085_0 (.nil)) (by decide) (by decide))

theorem cover229087 : P.CoversSplit 26 10 229087 0xffff0000ffff0000ffff0000ffff050000000000000000000000000000300000000000000000000005050000050500000000000000000000000000000000000000000000003300000000000000330000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 587, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c229087_0 : P.sumLeaves 26 234585088 1024 = 1028931305 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229087) (lo := 0) (len := 1024) (W := 1028931305) check rows elimOK (by decide) (by decide) cover229087 (by decide)
  decide +kernel

theorem h229087 : P.leaf 36 229087 = 1028931305 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1028931305)]) (.cons c229087_0 (.nil)) (by decide) (by decide))

theorem cover229101 : P.CoversSplit 26 10 229101 0xfffffffffffffffffffffffafffffafa00000000000000000000000000300000fffffffffffffffffffff0f0fffff0f00000000000000000000000000030000000000000003300330000000000330032000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c229101_0 : P.sumLeaves 26 234599424 735 = 85561512 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229101) (lo := 0) (len := 735) (W := 85561512) check rows elimOK (by decide) (by decide) cover229101 (by decide)
  decide +kernel

theorem c229101_1 : P.sumLeaves 26 234600159 228 = 178387807 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229101) (lo := 735) (len := 228) (W := 178387807) check rows elimOK (by decide) (by decide) cover229101 (by decide)
  decide +kernel

theorem c229101_2 : P.sumLeaves 26 234600387 61 = 254680938 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229101) (lo := 963) (len := 61) (W := 254680938) check rows elimOK (by decide) (by decide) cover229101 (by decide)
  decide +kernel

theorem h229101 : P.leaf 36 229101 = 518630257 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(735, 85561512), (228, 178387807), (61, 254680938)]) (.cons c229101_0 (.cons c229101_1 (.cons c229101_2 (.nil)))) (by decide) (by decide))

theorem cover229102 : P.CoversSplit 26 10 229102 0xfffffffffffffffffffffffafffffafa00000000000000000000000000300000fffffffffffffffffffff0f0fffff0f00000000000000000000000000030000000000000003300330000000000330032000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c229102_0 : P.sumLeaves 26 234600448 735 = 163944042 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229102) (lo := 0) (len := 735) (W := 163944042) check rows elimOK (by decide) (by decide) cover229102 (by decide)
  decide +kernel

theorem c229102_1 : P.sumLeaves 26 234601183 228 = 532880410 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229102) (lo := 735) (len := 228) (W := 532880410) check rows elimOK (by decide) (by decide) cover229102 (by decide)
  decide +kernel

theorem c229102_2 : P.sumLeaves 26 234601411 61 = 601266868 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229102) (lo := 963) (len := 61) (W := 601266868) check rows elimOK (by decide) (by decide) cover229102 (by decide)
  decide +kernel

theorem h229102 : P.leaf 36 229102 = 1298091320 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(735, 163944042), (228, 532880410), (61, 601266868)]) (.cons c229102_0 (.cons c229102_1 (.cons c229102_2 (.nil)))) (by decide) (by decide))

theorem cover229103 : P.CoversSplit 26 10 229103 0xfffffffffffffffffffffffafffffafa00000000000000000000000000300000fffffffffffffffffffff0f0fffff0f00000000000000000000000000030000000000000003300330000000000330032000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c229103_0 : P.sumLeaves 26 234601472 735 = 283780350 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229103) (lo := 0) (len := 735) (W := 283780350) check rows elimOK (by decide) (by decide) cover229103 (by decide)
  decide +kernel

theorem c229103_1 : P.sumLeaves 26 234602207 228 = 806341394 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229103) (lo := 735) (len := 228) (W := 806341394) check rows elimOK (by decide) (by decide) cover229103 (by decide)
  decide +kernel

theorem c229103_2 : P.sumLeaves 26 234602435 61 = 826236858 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229103) (lo := 963) (len := 61) (W := 826236858) check rows elimOK (by decide) (by decide) cover229103 (by decide)
  decide +kernel

theorem h229103 : P.leaf 36 229103 = 1916358602 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(735, 283780350), (228, 806341394), (61, 826236858)]) (.cons c229103_0 (.cons c229103_1 (.cons c229103_2 (.nil)))) (by decide) (by decide))

theorem cover229118 : P.CoversSplit 26 10 229118 0xfffffffffffffffffffffffafffffafa00000000000000000000000000300000fffffffffffffffffffff0f0fffff0f00000000000000000000000000030000000000000003300330000000000330032000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c229118_0 : P.sumLeaves 26 234616832 735 = 276207569 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229118) (lo := 0) (len := 735) (W := 276207569) check rows elimOK (by decide) (by decide) cover229118 (by decide)
  decide +kernel

theorem c229118_1 : P.sumLeaves 26 234617567 228 = 943128462 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229118) (lo := 735) (len := 228) (W := 943128462) check rows elimOK (by decide) (by decide) cover229118 (by decide)
  decide +kernel

theorem c229118_2 : P.sumLeaves 26 234617795 61 = 1038331120 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229118) (lo := 963) (len := 61) (W := 1038331120) check rows elimOK (by decide) (by decide) cover229118 (by decide)
  decide +kernel

theorem h229118 : P.leaf 36 229118 = 2257667151 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(735, 276207569), (228, 943128462), (61, 1038331120)]) (.cons c229118_0 (.cons c229118_1 (.cons c229118_2 (.nil)))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(229069, 360), (229071, 360), (229084, 360), (229085, 720), (229087, 360), (229101, 180), (229102, 720), (229103, 720), (229118, 360)]

theorem segOK : checkSeg 20 perms 229069 229119 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 229069 229119 4140 4478542648020 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 4478542648020)
    (SegSum.cons (w := 360) h229069 (SegSum.cons (w := 360) h229071 (SegSum.cons (w := 360) h229084 (SegSum.cons (w := 720) h229085 (SegSum.cons (w := 360) h229087 (SegSum.cons (w := 180) h229101 (SegSum.cons (w := 720) h229102 (SegSum.cons (w := 720) h229103 (SegSum.cons (w := 360) h229118 (show SegSum (P.leaf 36) [] 0 from rfl)))))))))) (by decide)

end RACert.S6N0.C0.S111
