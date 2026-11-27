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

namespace RACert.S4N1.C0.S100

open RACert RACert.Problem

theorem cover26607 : P.CoversSplit 24 10 26607 0xfffffffffafaaaaafffffffffafaaaaafffffffffafaaaaaffff000000000000ffccffccfac8aa88ccccccccc8c88888ffccffccfac8aa88cccc000000000000fffffffffafaaaaaffff0000fafa0000fffffffffafaaaaaffff000000000000ffcc0000fac80000cccc0000c8c80000ffcc0000fac80000cccc000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 1202, 1251, 1259, 1264, 1601]) (by decide +kernel)

noncomputable def f26607 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (27245568 + i)

theorem c26607_0 : rowSum f26607 0 413 = 107275132 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26607) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover26607 (by decide)
  decide +kernel

theorem c26607_1 : rowSum f26607 413 310 = 221542839 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26607) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover26607 (by decide)
  decide +kernel

theorem c26607_2 : rowSum f26607 723 301 = 274523021 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26607) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover26607 (by decide)
  decide +kernel

theorem sum26607 : rowSum f26607 0 1024 = 603340992 :=
  rowSum_append (F := f26607) (lo := 0) (n := 413) (m := 611) (A := 107275132) (B := 496065860) c26607_0 (rowSum_append (F := f26607) (lo := 413) (n := 310) (m := 301) (A := 221542839) (B := 274523021) c26607_1 (c26607_2))

theorem h26607 : P.leaf 34 26607 = 603340992 :=
  leaf_weighted (k := 24) (d := 10) (H := 26607) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 26607) (by decide) (by decide +kernel)) sum26607

theorem cover26623 : P.CoversSplit 24 10 26623 0xfffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaaffccffccfac8aa88ccccccccc8c88888ffccffccfac8aa88ccccccccc8c88888fffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaaffccffccfac8aa88ccccccccc8c88888ffccffccfac8aa88ccccccccc8c88888 :=
  coversSplit check rows (by decide) (by decide) (xs := [860, 915, 1202, 1259, 1601]) (by decide +kernel)

noncomputable def f26623 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (27261952 + i)

theorem c26623_0 : rowSum f26623 0 226 = 168140106 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26623) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover26623 (by decide)
  decide +kernel

theorem c26623_1 : rowSum f26623 226 206 = 264663788 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26623) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover26623 (by decide)
  decide +kernel

theorem c26623_2 : rowSum f26623 432 300 = 466013892 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26623) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover26623 (by decide)
  decide +kernel

theorem c26623_3 : rowSum f26623 732 292 = 477176811 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26623) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover26623 (by decide)
  decide +kernel

theorem sum26623 : rowSum f26623 0 1024 = 1375994597 :=
  rowSum_append (F := f26623) (lo := 0) (n := 226) (m := 798) (A := 168140106) (B := 1207854491) c26623_0 (rowSum_append (F := f26623) (lo := 226) (n := 206) (m := 592) (A := 264663788) (B := 943190703) c26623_1 (rowSum_append (F := f26623) (lo := 432) (n := 300) (m := 292) (A := 466013892) (B := 477176811) c26623_2 (c26623_3)))

theorem h26623 : P.leaf 34 26623 = 1375994597 :=
  leaf_weighted (k := 24) (d := 10) (H := 26623) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 26623) (by decide) (by decide +kernel)) sum26623

theorem cover28072 : P.CoversSplit 24 10 28072 0xaa000000ba00f0000000000000000000aa000000000000000000000000000000aa080000aa00e000888800008880c0c0aa080000000000008888000000000000aa000000ba00f0000000000000000000aa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 517, 522, 858, 865, 915]) (by decide +kernel)

noncomputable def f28072 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (28745728 + i)

theorem c28072_0 : rowSum f28072 0 1024 = 1108112 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 28072) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover28072 (by decide)
  decide +kernel

theorem sum28072 : rowSum f28072 0 1024 = 1108112 :=
  c28072_0

theorem h28072 : P.leaf 34 28072 = 1108112 :=
  leaf_weighted (k := 24) (d := 10) (H := 28072) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 28072) (by decide) (by decide +kernel)) sum28072

theorem cover28073 : P.CoversSplit 24 10 28073 0xaa000000ba0000000000000000000000aa000000000000000000000000000000aa000000ba0000000000000000000000aa000000000000000000000000000000aa000000ba0000000000000000000000aa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 517, 522, 858, 865, 915, 1202, 1210, 1259, 1601]) (ps := [(11, [858], [472])]) (by decide +kernel)

theorem c28073_0 : P.sumLeaves 24 28746752 1024 = 8155784 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28073) (lo := 0) (len := 1024) (W := 8155784) check rows elimOK (by decide) (by decide) cover28073 (by decide)
  decide +kernel

theorem h28073 : P.leaf 34 28073 = 8155784 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8155784)]) (.cons c28073_0 (.nil)) (by decide) (by decide))

theorem cover28075 : P.CoversSplit 24 10 28075 0xaa000000aa0000000000000000000000aa000000000000000000000000000000aa000000aa0000000000000000000000aa000000000000000000000000000000aa000000aa0000000000000000000000aa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 858, 865, 1202, 1210, 1259, 1601]) (by decide +kernel)

noncomputable def f28075 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (28748800 + i)

theorem c28075_0 : rowSum f28075 0 1024 = 36762444 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 28075) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover28075 (by decide)
  decide +kernel

theorem sum28075 : rowSum f28075 0 1024 = 36762444 :=
  c28075_0

theorem h28075 : P.leaf 34 28075 = 36762444 :=
  leaf_weighted (k := 24) (d := 10) (H := 28075) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 28075) (by decide) (by decide +kernel)) sum28075

theorem cover28076 : P.CoversSplit 24 10 28076 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [472]) (by decide +kernel)

theorem c28076_0 : P.sumLeaves 24 28749824 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28076) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover28076 (by decide)
  decide +kernel

theorem h28076 : P.leaf 34 28076 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c28076_0 (.nil)) (by decide) (by decide))

theorem cover28077 : P.CoversSplit 24 10 28077 0xaa000000ba00f0000000000000000000aa000000000000000000000000000000aa000000ba00f0000000000000000000aa000000000000000000000000000000aa000000ba00f0000000000000000000aa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 517, 522, 858, 865, 915, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c28077_0 : P.sumLeaves 24 28750848 1024 = 15834606 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28077) (lo := 0) (len := 1024) (W := 15834606) check rows elimOK (by decide) (by decide) cover28077 (by decide)
  decide +kernel

theorem h28077 : P.leaf 34 28077 = 15834606 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 15834606)]) (.cons c28077_0 (.nil)) (by decide) (by decide))

theorem cover28079 : P.CoversSplit 24 10 28079 0xaa000000aa0000000000000000000000aa000000000000000000000000000000aa000000aa0000000000000000000000aa000000000000000000000000000000aa000000aa0000000000000000000000aa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 858, 865, 1202, 1210, 1259, 1601]) (by decide +kernel)

noncomputable def f28079 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (28752896 + i)

theorem c28079_0 : rowSum f28079 0 1024 = 42132004 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 28079) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover28079 (by decide)
  decide +kernel

theorem sum28079 : rowSum f28079 0 1024 = 42132004 :=
  c28079_0

theorem h28079 : P.leaf 34 28079 = 42132004 :=
  leaf_weighted (k := 24) (d := 10) (H := 28079) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 28079) (by decide) (by decide +kernel)) sum28079

theorem cover28090 : P.CoversSplit 24 10 28090 0xfffffffffafaf0f0fffffffffafaf0f0fffffffffafaf0f0ffff000000000000ffc0ffc0fac0f0c0cc00cc00c800c000ffc0ffc0fac0f0c0cc00000000000000fffffffffafaf0f0fffffffffafaf0f0fffffffffafaf0f0ffff000000000000ffc0ffc0fac0f0c0cc00cc00c800c000ffc0ffc0f000f000cc00000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 858, 865, 1202, 1251, 1259, 1601]) (ps := [(8, [1217, 1609], [1272])]) (by decide +kernel)

theorem c28090_0 : P.sumLeaves 24 28764160 325 = 6288737 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28090) (lo := 0) (len := 325) (W := 6288737) check rows elimOK (by decide) (by decide) cover28090 (by decide)
  decide +kernel

theorem c28090_1 : P.sumLeaves 24 28764485 116 = 8393071 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28090) (lo := 325) (len := 116) (W := 8393071) check rows elimOK (by decide) (by decide) cover28090 (by decide)
  decide +kernel

theorem c28090_2 : P.sumLeaves 24 28764601 198 = 28680384 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28090) (lo := 441) (len := 198) (W := 28680384) check rows elimOK (by decide) (by decide) cover28090 (by decide)
  decide +kernel

theorem c28090_3 : P.sumLeaves 24 28764799 237 = 30097400 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28090) (lo := 639) (len := 237) (W := 30097400) check rows elimOK (by decide) (by decide) cover28090 (by decide)
  decide +kernel

theorem c28090_4 : P.sumLeaves 24 28765036 120 = 41502752 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28090) (lo := 876) (len := 120) (W := 41502752) check rows elimOK (by decide) (by decide) cover28090 (by decide)
  decide +kernel

theorem c28090_5 : P.sumLeaves 24 28765156 28 = 30672338 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28090) (lo := 996) (len := 28) (W := 30672338) check rows elimOK (by decide) (by decide) cover28090 (by decide)
  decide +kernel

theorem h28090 : P.leaf 34 28090 = 145634682 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(325, 6288737), (116, 8393071), (198, 28680384), (237, 30097400), (120, 41502752), (28, 30672338)]) (.cons c28090_0 (.cons c28090_1 (.cons c28090_2 (.cons c28090_3 (.cons c28090_4 (.cons c28090_5 (.nil))))))) (by decide) (by decide))

theorem cover28091 : P.CoversSplit 24 10 28091 0xfffffffffafaf0f0fffffffffafaf0f0fffffffffafaf0f0ffff000000000000ffccffccfac8f0c0ccccccccc8c8c0c0ffccffccfac8f0c0cccc000000000000fffffffffafaf0f0fffffffffafaf0f0fffffffffafaf0f0ffff000000000000ffccffccfac8f0c0ccccccccc8c8c0c0ffccffccf000f000cccc000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 858, 865, 1202, 1251, 1259, 1601]) (ps := [(8, [1217, 1609], [1272])]) (by decide +kernel)

theorem c28091_0 : P.sumLeaves 24 28765184 247 = 16819486 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28091) (lo := 0) (len := 247) (W := 16819486) check rows elimOK (by decide) (by decide) cover28091 (by decide)
  decide +kernel

theorem c28091_1 : P.sumLeaves 24 28765431 168 = 26110824 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28091) (lo := 247) (len := 168) (W := 26110824) check rows elimOK (by decide) (by decide) cover28091 (by decide)
  decide +kernel

theorem c28091_2 : P.sumLeaves 24 28765599 174 = 64746050 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28091) (lo := 415) (len := 174) (W := 64746050) check rows elimOK (by decide) (by decide) cover28091 (by decide)
  decide +kernel

theorem c28091_3 : P.sumLeaves 24 28765773 174 = 64925253 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28091) (lo := 589) (len := 174) (W := 64925253) check rows elimOK (by decide) (by decide) cover28091 (by decide)
  decide +kernel

theorem c28091_4 : P.sumLeaves 24 28765947 168 = 74791130 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28091) (lo := 763) (len := 168) (W := 74791130) check rows elimOK (by decide) (by decide) cover28091 (by decide)
  decide +kernel

theorem c28091_5 : P.sumLeaves 24 28766115 93 = 112007411 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28091) (lo := 931) (len := 93) (W := 112007411) check rows elimOK (by decide) (by decide) cover28091 (by decide)
  decide +kernel

theorem h28091 : P.leaf 34 28091 = 359400154 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(247, 16819486), (168, 26110824), (174, 64746050), (174, 64925253), (168, 74791130), (93, 112007411)]) (.cons c28091_0 (.cons c28091_1 (.cons c28091_2 (.cons c28091_3 (.cons c28091_4 (.cons c28091_5 (.nil))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(26607, 24), (26623, 8), (28072, 6), (28073, 24), (28075, 24), (28076, 24), (28077, 48), (28079, 24), (28090, 12), (28091, 24)]

theorem segOK : checkSeg 16 perms 26607 28092 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 26607 28092 218 38717275792 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 38717275792)
    (SegSum.cons (w := 24) h26607 (SegSum.cons (w := 8) h26623 (SegSum.cons (w := 6) h28072 (SegSum.cons (w := 24) h28073 (SegSum.cons (w := 24) h28075 (SegSum.cons (w := 24) h28076 (SegSum.cons (w := 48) h28077 (SegSum.cons (w := 24) h28079 (SegSum.cons (w := 12) h28090 (SegSum.cons (w := 24) h28091 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))) (by decide)

end RACert.S4N1.C0.S100
