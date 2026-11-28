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

namespace RACert.S4N1.C0.S66

open RACert RACert.Problem

theorem cover23340 : P.CoversSplit 24 10 23340 0x8000000088008000000000000000000080000000000000000000000000000000808000008888808080000000880080008080000000000000800000000000000080000000880080000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 517, 522, 529, 572, 859, 879, 1202, 1601]) (by decide +kernel)

theorem h23340 : P.leaf 34 23340 = 1673420 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 23340) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 23340) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 23340) (weight := rowWeight keep1 twice1) (xs := [0, 383, 463, 475, 479, 511, 575, 631, 639, 655, 667, 671, 703, 711, 719, 723, 727, 731, 735, 759, 767, 895, 975, 987, 991, 1023]) check rows elimOK (by decide) (by decide) cover23340 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h22372 : P.leaf 34 22372 = 1673420 :=
  orient4 (v := 23340) (by decide) (by decide +kernel) h23340

theorem cover27947 : P.CoversSplit 24 10 27947 0x8800000088000000000000000000000088000000000000000000000000000000880000008800000000000000000000008800000000000000000000000000000088000000880000000000000000000000880000000000000000000000000000000000000000000000002200000022000000000000000000000022000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 529, 572, 858, 865, 1202, 1210]) (by decide +kernel)

theorem h27947 : P.leaf 34 27947 = 8049995 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 27947) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 27947) (weight := fun _ => 1) (xs := [49, 53, 145, 149, 177, 181, 379, 383, 475, 479, 507, 511, 635, 639, 731, 735, 763, 767, 891, 895, 987, 991, 1019, 1023]) check rows elimOK (by decide) (by decide) cover27947 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h22373 : P.leaf 34 22373 = 8049995 :=
  orient5 (v := 27947) (by decide) (by decide +kernel) h27947

theorem cover23356 : P.CoversSplit 24 10 23356 0xfca9fca9a8a8a0a0fca9fca9a8a8a0a0f0a0f4a100000000f0a0f4a100000000cc88cc8888888080cc00cc0088008000c080c48000000000c000c40000000000fc00fc00a800a000fc21fc21a820a020f000f40000000000f020f421000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 529, 859, 879, 916, 1202, 1259, 1601]) (by decide +kernel)

noncomputable def f23356 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (23916544 + i)

theorem c23356_0 : rowSum f23356 0 1008 = 47684844 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 23356) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover23356 (by decide)
  decide +kernel

theorem c23356_1 : rowSum f23356 1008 16 = 8127916 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 23356) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover23356 (by decide)
  decide +kernel

theorem sum23356 : rowSum f23356 0 1024 = 55812760 :=
  rowSum_append (F := f23356) (lo := 0) (n := 1008) (m := 16) (A := 47684844) (B := 8127916) c23356_0 (c23356_1)

theorem h23356 : P.leaf 34 23356 = 55812760 :=
  leaf_weighted (k := 24) (d := 10) (H := 23356) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 23356) (by decide) (by decide +kernel)) sum23356

theorem h22374 : P.leaf 34 22374 = 55812760 :=
  orient4 (v := 23356) (by decide) (by decide +kernel) h23356

theorem cover23357 : P.CoversSplit 24 10 23357 0xffffffffaaaaa0a0ffffffffaaaaa0a0ffffffff00000000ffffffff00000000cccccccc88888080cc00cc0088008000cccccccc00000000cc00cc0000000000ff00ff00aa00a000ff33ff33aa22a020ff00ff0000000000ff33ff33000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 517, 529, 879, 916, 1202, 1259, 1601]) (by decide +kernel)

theorem c23357_0 : P.sumLeaves 24 23917568 555 = 23085857 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23357) (lo := 0) (len := 555) (W := 23085857) check rows elimOK (by decide) (by decide) cover23357 (by decide)
  decide +kernel

theorem c23357_1 : P.sumLeaves 24 23918123 317 = 27593379 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23357) (lo := 555) (len := 317) (W := 27593379) check rows elimOK (by decide) (by decide) cover23357 (by decide)
  decide +kernel

theorem c23357_2 : P.sumLeaves 24 23918440 136 = 60945416 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23357) (lo := 872) (len := 136) (W := 60945416) check rows elimOK (by decide) (by decide) cover23357 (by decide)
  decide +kernel

theorem c23357_3 : P.sumLeaves 24 23918576 16 = 17477014 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23357) (lo := 1008) (len := 16) (W := 17477014) check rows elimOK (by decide) (by decide) cover23357 (by decide)
  decide +kernel

theorem h23357 : P.leaf 34 23357 = 129101666 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(555, 23085857), (317, 27593379), (136, 60945416), (16, 17477014)]) (.cons c23357_0 (.cons c23357_1 (.cons c23357_2 (.cons c23357_3 (.nil))))) (by decide) (by decide))

theorem h22375 : P.leaf 34 22375 = 129101666 :=
  orient4 (v := 23357) (by decide) (by decide +kernel) h23357

theorem cover23404 : P.CoversSplit 24 10 23404 0xcc00cc00880088000000000000000000c0000000000000000000000000000000cccccccc88808880cc00cc0088008800c0c0000000000000c000000000000000cc00cc00880088000000000000000000c00044000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 522, 572, 859, 879, 1202, 1210, 1601]) (ps := [(2, [465], [473])]) (by decide +kernel)

theorem c23404_0 : P.sumLeaves 24 23965696 1024 = 9897440 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23404) (lo := 0) (len := 1024) (W := 9897440) check rows elimOK (by decide) (by decide) cover23404 (by decide)
  decide +kernel

theorem h23404 : P.leaf 34 23404 = 9897440 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 9897440)]) (.cons c23404_0 (.nil)) (by decide) (by decide))

theorem h22380 : P.leaf 34 22380 = 9897440 :=
  orient4 (v := 23404) (by decide) (by decide +kernel) h23404

theorem cover23405 : P.CoversSplit 24 10 23405 0xcc00cc00880088000000000000000000cc000000000000000000000000000000cc00cc00880088000000000000000000cc000000000000000000000000000000cc00cc00880088000000000000000000cc0044000000000000000000000000000000000000000000003300330022002200000000000000000033000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 522, 572, 879, 916, 1202, 1210, 1601]) (ps := [(18, [921], [1210])]) (by decide +kernel)

theorem c23405_0 : P.sumLeaves 24 23966720 1024 = 20770908 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23405) (lo := 0) (len := 1024) (W := 20770908) check rows elimOK (by decide) (by decide) cover23405 (by decide)
  decide +kernel

theorem h23405 : P.leaf 34 23405 = 20770908 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 20770908)]) (.cons c23405_0 (.nil)) (by decide) (by decide))

theorem h22381 : P.leaf 34 22381 = 20770908 :=
  orient4 (v := 23405) (by decide) (by decide +kernel) h23405

theorem cover23420 : P.CoversSplit 24 10 23420 0xfcfcfcfca8a8a8a8fcfcfcfca8a8a8a8f0f0f4f400000000f0f0f4f400000000cccccccc88888888cc00cc0088008800c0c0c4c400000000c000c40000000000fc00fc00a800a800fc30fc30a820a820f000f40000000000f030f430000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 859, 879, 916, 1202, 1259, 1601]) (by decide +kernel)

theorem c23420_0 : P.sumLeaves 24 23982080 727 = 19863531 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23420) (lo := 0) (len := 727) (W := 19863531) check rows elimOK (by decide) (by decide) cover23420 (by decide)
  decide +kernel

theorem c23420_1 : P.sumLeaves 24 23982807 248 = 46239429 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23420) (lo := 727) (len := 248) (W := 46239429) check rows elimOK (by decide) (by decide) cover23420 (by decide)
  decide +kernel

theorem c23420_2 : P.sumLeaves 24 23983055 49 = 28576750 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23420) (lo := 975) (len := 49) (W := 28576750) check rows elimOK (by decide) (by decide) cover23420 (by decide)
  decide +kernel

theorem h23420 : P.leaf 34 23420 = 94679710 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(727, 19863531), (248, 46239429), (49, 28576750)]) (.cons c23420_0 (.cons c23420_1 (.cons c23420_2 (.nil)))) (by decide) (by decide))

theorem h22382 : P.leaf 34 22382 = 94679710 :=
  orient4 (v := 23420) (by decide) (by decide +kernel) h23420

theorem cover23421 : P.CoversSplit 24 10 23421 0xffffffffaaaaaaaaffffffffaaaaaaaaffffffff00000000ffffffff00000000cccccccc88888888cc00cc0088008800cccccccc00000000cc00cc0000000000ff00ff00aa00aa00ff33ff33aa22aa22ff00ff0000000000ff33ff33000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 859, 879, 916, 1202, 1259, 1601]) (by decide +kernel)

theorem c23421_0 : P.sumLeaves 24 23983104 508 = 28745681 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23421) (lo := 0) (len := 508) (W := 28745681) check rows elimOK (by decide) (by decide) cover23421 (by decide)
  decide +kernel

theorem c23421_1 : P.sumLeaves 24 23983612 356 = 46478482 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23421) (lo := 508) (len := 356) (W := 46478482) check rows elimOK (by decide) (by decide) cover23421 (by decide)
  decide +kernel

theorem c23421_2 : P.sumLeaves 24 23983968 128 = 70626219 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23421) (lo := 864) (len := 128) (W := 70626219) check rows elimOK (by decide) (by decide) cover23421 (by decide)
  decide +kernel

theorem c23421_3 : P.sumLeaves 24 23984096 32 = 48514815 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23421) (lo := 992) (len := 32) (W := 48514815) check rows elimOK (by decide) (by decide) cover23421 (by decide)
  decide +kernel

theorem h23421 : P.leaf 34 23421 = 194365197 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(508, 28745681), (356, 46478482), (128, 70626219), (32, 48514815)]) (.cons c23421_0 (.cons c23421_1 (.cons c23421_2 (.cons c23421_3 (.nil))))) (by decide) (by decide))

theorem h22383 : P.leaf 34 22383 = 194365197 :=
  orient4 (v := 23421) (by decide) (by decide +kernel) h23421

theorem cover23343 : P.CoversSplit 24 10 23343 0xffffffffaaaaa0a0ffffffffaaaaa0a0ffff000000000000ffff000000000000cccccccc88888080cc00cc0088008000cccc000000000000cc00000000000000ffffffffaaaaa0a00000000000000000ffff55550000000033330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 1202, 1210, 1259, 1308, 1601]) (ps := [(17, [1251], [1259])]) (by decide +kernel)

noncomputable def f23343 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (23903232 + i)

theorem c23343_0 : rowSum f23343 0 933 = 42388285 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 23343) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover23343 (by decide)
  decide +kernel

theorem c23343_1 : rowSum f23343 933 91 = 39336312 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 23343) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover23343 (by decide)
  decide +kernel

theorem sum23343 : rowSum f23343 0 1024 = 81724597 :=
  rowSum_append (F := f23343) (lo := 0) (n := 933) (m := 91) (A := 42388285) (B := 39336312) c23343_0 (c23343_1)

theorem h23343 : P.leaf 34 23343 = 81724597 :=
  leaf_weighted (k := 24) (d := 10) (H := 23343) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 23343) (by decide) (by decide +kernel)) sum23343

theorem h22389 : P.leaf 34 22389 = 81724597 :=
  orient4 (v := 23343) (by decide) (by decide +kernel) h23343

theorem cover23359 : P.CoversSplit 24 10 23359 0xffffffffaaaaa0a0ffffffffaaaaa0a0ffffffff0000a0a0ffffffff0000a0a0cccccccc88888080cc00cc0088008000cccccccc00008080cc00cc0000008000ffffffffaaaaa0a0ffffffffaaaaa0a0ffffffff00000000ffffffff000000000000000000000000cc00cc008800800000000000888880800000000088008000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 572, 1202, 1217, 1259, 1308, 1601, 1609]) (by decide +kernel)

noncomputable def f23359 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (23919616 + i)

theorem c23359_0 : rowSum f23359 0 447 = 52901387 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 23359) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover23359 (by decide)
  decide +kernel

theorem c23359_1 : rowSum f23359 447 508 = 165593804 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 23359) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover23359 (by decide)
  decide +kernel

theorem c23359_2 : rowSum f23359 955 69 = 62366493 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 23359) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover23359 (by decide)
  decide +kernel

theorem sum23359 : rowSum f23359 0 1024 = 280861684 :=
  rowSum_append (F := f23359) (lo := 0) (n := 447) (m := 577) (A := 52901387) (B := 227960297) c23359_0 (rowSum_append (F := f23359) (lo := 447) (n := 508) (m := 69) (A := 165593804) (B := 62366493) c23359_1 (c23359_2))

theorem h23359 : P.leaf 34 23359 = 280861684 :=
  leaf_weighted (k := 24) (d := 10) (H := 23359) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 23359) (by decide) (by decide +kernel)) sum23359

theorem h22391 : P.leaf 34 22391 = 280861684 :=
  orient4 (v := 23359) (by decide) (by decide +kernel) h23359

def seg : List (ℕ × ℕ) := [(22372, 24), (22373, 48), (22374, 24), (22375, 48), (22380, 48), (22381, 48), (22382, 48), (22383, 48), (22389, 24), (22391, 24)]

theorem segOK : checkSeg 16 perms 22372 22396 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 22372 22396 384 32011255032 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 32011255032)
    (SegSum.cons (w := 24) h22372 (SegSum.cons (w := 48) h22373 (SegSum.cons (w := 24) h22374 (SegSum.cons (w := 48) h22375 (SegSum.cons (w := 48) h22380 (SegSum.cons (w := 48) h22381 (SegSum.cons (w := 48) h22382 (SegSum.cons (w := 48) h22383 (SegSum.cons (w := 24) h22389 (SegSum.cons (w := 24) h22391 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))) (by decide)

end RACert.S4N1.C0.S66
