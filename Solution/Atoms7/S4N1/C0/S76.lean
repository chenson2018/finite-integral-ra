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

namespace RACert.S4N1.C0.S76

open RACert RACert.Problem

theorem cover24318 : P.CoversSplit 24 10 24318 0xfffffffffafa0000fffffffffafa0000fffffffffafa0000fffffffffafa00000000000000000000000000000000000000000000000000000000000000000000cc00cc00c80000000000000000000000cc00cc008000000000330033002000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 573, 916, 1202, 1210, 1259, 1308, 1601, 1651]) (ps := [(8, [1217], [573, 1266]), (14, [1217], [916, 1266])]) (by decide +kernel)

noncomputable def f24318 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (24901632 + i)

theorem c24318_0 : rowSum f24318 0 947 = 78120007 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 24318) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover24318 (by decide)
  decide +kernel

theorem c24318_1 : rowSum f24318 947 77 = 70249792 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 24318) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover24318 (by decide)
  decide +kernel

theorem sum24318 : rowSum f24318 0 1024 = 148369799 :=
  rowSum_append (F := f24318) (lo := 0) (n := 947) (m := 77) (A := 78120007) (B := 70249792) c24318_0 (c24318_1)

theorem h24318 : P.leaf 34 24318 = 148369799 :=
  leaf_weighted (k := 24) (d := 10) (H := 24318) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 24318) (by decide) (by decide +kernel)) sum24318

theorem cover24319 : P.CoversSplit 24 10 24319 0xfffffffffafa0000fffffffffafa0000fffffffffafa0000fffffffffafa00000000000000000000000000000000000000000000000000000000000000000000cc00cc00c80000000000000000000000cc00cc008000000000330033002000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [573, 916, 1202, 1210, 1259, 1308, 1601, 1651]) (ps := [(8, [1217], [573, 1266]), (14, [1217], [916, 1266])]) (by decide +kernel)

noncomputable def f24319 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (24902656 + i)

theorem c24319_0 : rowSum f24319 0 947 = 78129461 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 24319) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover24319 (by decide)
  decide +kernel

theorem c24319_1 : rowSum f24319 947 77 = 70249792 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 24319) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover24319 (by decide)
  decide +kernel

theorem sum24319 : rowSum f24319 0 1024 = 148379253 :=
  rowSum_append (F := f24319) (lo := 0) (n := 947) (m := 77) (A := 78129461) (B := 70249792) c24319_0 (c24319_1)

theorem h24319 : P.leaf 34 24319 = 148379253 :=
  leaf_weighted (k := 24) (d := 10) (H := 24319) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 24319) (by decide) (by decide +kernel)) sum24319

theorem cover25903 : P.CoversSplit 24 10 25903 0x8000000080000000000000000000000080000000000004000000000000000000800000008000000000000000000000008000000000000400000000000000000080000000800000000000000000000000800000000000000000000000000000000000000000000000002000000020000000000000000000000000000000000001 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 529, 572, 858, 865, 1202]) (by decide +kernel)

theorem h25903 : P.leaf 34 25903 = 4733090 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 25903) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 25903) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 25903) (weight := rowWeight keep1 twice1) (xs := [0, 149, 181, 383, 479, 511, 586, 639, 735, 767, 842, 895, 991, 1023]) check rows elimOK (by decide) (by decide) cover25903 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h24357 : P.leaf 34 24357 = 4733090 :=
  orient5 (v := 25903) (by decide) (by decide +kernel) h25903

theorem cover25919 : P.CoversSplit 24 10 25919 0xfffffffffafa0000fffffffffafa0000f000f50000000000f000000000000000ffccffccfac800000000000000000000f000f500000000000000000000000000f000f000f0000000f0300000f0300000f000f00000000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 529, 572, 858, 860, 865, 872, 915, 1202, 1251, 1259, 1264, 1308, 1601]) (by decide +kernel)

noncomputable def f25919 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (26541056 + i)

theorem c25919_0 : rowSum f25919 0 1023 = 88617480 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 25919) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover25919 (by decide)
  decide +kernel

theorem c25919_1 : rowSum f25919 1023 1 = 3374356 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 25919) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover25919 (by decide)
  decide +kernel

theorem sum25919 : rowSum f25919 0 1024 = 91991836 :=
  rowSum_append (F := f25919) (lo := 0) (n := 1023) (m := 1) (A := 88617480) (B := 3374356) c25919_0 (c25919_1)

theorem h25919 : P.leaf 34 25919 = 91991836 :=
  leaf_weighted (k := 24) (d := 10) (H := 25919) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 25919) (by decide) (by decide +kernel)) sum25919

theorem h24359 : P.leaf 34 24359 = 91991836 :=
  orient5 (v := 25919) (by decide) (by decide +kernel) h25919

theorem cover25966 : P.CoversSplit 24 10 25966 0xc0000000c00000000000000000000000c0000000000000000000000000000000d0000000d00000000000000000000000d0000000000000000000000000000000c0000000c00000000000000000000000c00000000000000000000000000000000000000000000000003000000030000000000000000000000030000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 522, 572, 858, 860, 865, 872, 915, 1202, 1601]) (by decide +kernel)

theorem h25966 : P.leaf 34 25966 = 3537016 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 25966) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 25966) (weight := fun _ => 1) (xs := [52, 53, 148, 149, 180, 181, 382, 383, 478, 479, 510, 511, 636, 638, 639, 732, 734, 735, 764, 766, 767, 894, 895, 990, 991, 1022, 1023]) check rows elimOK (by decide) (by decide) cover25966 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h24364 : P.leaf 34 24364 = 3537016 :=
  orient5 (v := 25966) (by decide) (by decide +kernel) h25966

theorem cover25967 : P.CoversSplit 24 10 25967 0xc0000000c00000000000000000000000c0000000000000000000000000000000c0000000c00000000000000000000000c0000000000000000000000000000000c0000000c00000000000000000000000c00000000000000000000000000000000000000000000000003000000030000000000000000000000030000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 572, 858, 865, 1202, 1210]) (by decide +kernel)

theorem h25967 : P.leaf 34 25967 = 15081633 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 25967) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 25967) (weight := fun _ => 1) (xs := [52, 53, 148, 149, 180, 181, 382, 383, 478, 479, 510, 511, 638, 639, 734, 735, 766, 767, 894, 895, 990, 991, 1022, 1023]) check rows elimOK (by decide) (by decide) cover25967 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h24365 : P.leaf 34 24365 = 15081633 :=
  orient5 (v := 25967) (by decide) (by decide +kernel) h25967

theorem cover39403 : P.CoversSplit 24 10 39403 0xf0000000f00000000000000000000000f0000000000000000000000000000000f0000000f00000000000000000000000f0000000000000000000000000000000f0000000f00000000000000000000000f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [466, 515, 522, 858, 865, 1202, 1209, 1258, 1601]) (by decide +kernel)

theorem c39403_0 : P.sumLeaves 24 40348672 1024 = 24259907 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 39403) (lo := 0) (len := 1024) (W := 24259907) check rows elimOK (by decide) (by decide) cover39403 (by decide)
  decide +kernel

theorem h39403 : P.leaf 34 39403 = 24259907 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 24259907)]) (.cons c39403_0 (.nil)) (by decide) (by decide))

theorem h24366 : P.leaf 34 24366 = 24259907 :=
  orient25 (v := 39403) (by decide) (by decide +kernel) h39403

theorem cover25983 : P.CoversSplit 24 10 25983 0xfffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaaffccffccfac8aa880000000000000000ffccffccfac8aa880000000000000000f000f000f000a000f0300000f0300000f000f00000000000f0300000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [572, 858, 865, 872, 915, 1202, 1259, 1264, 1308, 1601]) (by decide +kernel)

theorem c25983_0 : P.sumLeaves 24 26606592 742 = 39726145 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 25983) (lo := 0) (len := 742) (W := 39726145) check rows elimOK (by decide) (by decide) cover25983 (by decide)
  decide +kernel

theorem c25983_1 : P.sumLeaves 24 26607334 124 = 40804632 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 25983) (lo := 742) (len := 124) (W := 40804632) check rows elimOK (by decide) (by decide) cover25983 (by decide)
  decide +kernel

theorem c25983_2 : P.sumLeaves 24 26607458 119 = 84174429 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 25983) (lo := 866) (len := 119) (W := 84174429) check rows elimOK (by decide) (by decide) cover25983 (by decide)
  decide +kernel

theorem c25983_3 : P.sumLeaves 24 26607577 39 = 57257325 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 25983) (lo := 985) (len := 39) (W := 57257325) check rows elimOK (by decide) (by decide) cover25983 (by decide)
  decide +kernel

theorem h25983 : P.leaf 34 25983 = 221962531 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(742, 39726145), (124, 40804632), (119, 84174429), (39, 57257325)]) (.cons c25983_0 (.cons c25983_1 (.cons c25983_2 (.cons c25983_3 (.nil))))) (by decide) (by decide))

theorem h24367 : P.leaf 34 24367 = 221962531 :=
  orient5 (v := 25983) (by decide) (by decide +kernel) h25983

theorem cover26431 : P.CoversSplit 24 10 26431 0xfffffffffafa0000fffffffffafa0000ffffffff00000000ffff000000000000ffccffccfac800000000000000000000ffccffcc000000000000000000000000fffffffffafa0000ffff0000fafa0000ffffffff00000000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 529, 572, 872, 1202, 1217, 1251, 1259, 1264, 1308, 1601, 1609]) (ps := [(8, [615], [1217, 1272])]) (by decide +kernel)

noncomputable def f26431 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (27065344 + i)

theorem c26431_0 : rowSum f26431 0 510 = 119873479 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26431) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover26431 (by decide)
  decide +kernel

theorem c26431_1 : rowSum f26431 510 514 = 179168095 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26431) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover26431 (by decide)
  decide +kernel

theorem sum26431 : rowSum f26431 0 1024 = 299041574 :=
  rowSum_append (F := f26431) (lo := 0) (n := 510) (m := 514) (A := 119873479) (B := 179168095) c26431_0 (c26431_1)

theorem h26431 : P.leaf 34 26431 = 299041574 :=
  leaf_weighted (k := 24) (d := 10) (H := 26431) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 26431) (by decide) (by decide +kernel)) sum26431

theorem h24375 : P.leaf 34 24375 = 299041574 :=
  orient5 (v := 26431) (by decide) (by decide +kernel) h26431

theorem cover24380 : P.CoversSplit 24 10 24380 0xffaaffaafaaaa0a0ffaaffaafaaaa0a0ffaaffaac8888080ffaaffaac8888080cc88cc8888888080cc00cc0088008000cc88cc8888888080cc00cc0088008000ff00ff00fa00a000ff22ff22fa22a020ff00ff00c8008000ff22ff22c80080000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 529, 916, 1202, 1210, 1308, 1601]) (by decide +kernel)

theorem c24380_0 : P.sumLeaves 24 24965120 509 = 16490527 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24380) (lo := 0) (len := 509) (W := 16490527) check rows elimOK (by decide) (by decide) cover24380 (by decide)
  decide +kernel

theorem c24380_1 : P.sumLeaves 24 24965629 350 = 24618233 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24380) (lo := 509) (len := 350) (W := 24618233) check rows elimOK (by decide) (by decide) cover24380 (by decide)
  decide +kernel

theorem c24380_2 : P.sumLeaves 24 24965979 158 = 62791423 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24380) (lo := 859) (len := 158) (W := 62791423) check rows elimOK (by decide) (by decide) cover24380 (by decide)
  decide +kernel

theorem c24380_3 : P.sumLeaves 24 24966137 7 = 11500180 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24380) (lo := 1017) (len := 7) (W := 11500180) check rows elimOK (by decide) (by decide) cover24380 (by decide)
  decide +kernel

theorem h24380 : P.leaf 34 24380 = 115400363 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(509, 16490527), (350, 24618233), (158, 62791423), (7, 11500180)]) (.cons c24380_0 (.cons c24380_1 (.cons c24380_2 (.cons c24380_3 (.nil))))) (by decide) (by decide))

theorem cover26479 : P.CoversSplit 24 10 26479 0xfffffffffafaaaaafffffffffafaaaaafffffffffafaaaaaffff000000000000ffccffccfac8aa880000000000000000ffccffccfac8aa880000000000000000ccccccccc8c88888ccff0000c8fa0000cccccccc00000000ccff0000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 572, 872, 1202, 1251, 1259, 1264, 1308, 1601]) (by decide +kernel)

theorem c26479_0 : P.sumLeaves 24 27114496 618 = 34949021 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 26479) (lo := 0) (len := 618) (W := 34949021) check rows elimOK (by decide) (by decide) cover26479 (by decide)
  decide +kernel

theorem c26479_1 : P.sumLeaves 24 27115114 249 = 44100789 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 26479) (lo := 618) (len := 249) (W := 44100789) check rows elimOK (by decide) (by decide) cover26479 (by decide)
  decide +kernel

theorem c26479_2 : P.sumLeaves 24 27115363 120 = 73266096 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 26479) (lo := 867) (len := 120) (W := 73266096) check rows elimOK (by decide) (by decide) cover26479 (by decide)
  decide +kernel

theorem c26479_3 : P.sumLeaves 24 27115483 37 = 63835592 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 26479) (lo := 987) (len := 37) (W := 63835592) check rows elimOK (by decide) (by decide) cover26479 (by decide)
  decide +kernel

theorem h26479 : P.leaf 34 26479 = 216151498 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(618, 34949021), (249, 44100789), (120, 73266096), (37, 63835592)]) (.cons c26479_0 (.cons c26479_1 (.cons c26479_2 (.cons c26479_3 (.nil))))) (by decide) (by decide))

theorem h24381 : P.leaf 34 24381 = 216151498 :=
  orient5 (v := 26479) (by decide) (by decide +kernel) h26479

def seg : List (ℕ × ℕ) := [(24318, 8), (24319, 8), (24357, 12), (24359, 24), (24364, 48), (24365, 48), (24366, 48), (24367, 48), (24375, 12), (24380, 48), (24381, 48)]

theorem segOK : checkSeg 16 perms 24318 24382 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 24318 24382 352 36853953952 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 36853953952)
    (SegSum.cons (w := 8) h24318 (SegSum.cons (w := 8) h24319 (SegSum.cons (w := 12) h24357 (SegSum.cons (w := 24) h24359 (SegSum.cons (w := 48) h24364 (SegSum.cons (w := 48) h24365 (SegSum.cons (w := 48) h24366 (SegSum.cons (w := 48) h24367 (SegSum.cons (w := 12) h24375 (SegSum.cons (w := 48) h24380 (SegSum.cons (w := 48) h24381 (show SegSum (P.leaf 34) [] 0 from rfl)))))))))))) (by decide)

end RACert.S4N1.C0.S76
