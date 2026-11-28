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

namespace RACert.S4N1.C0.S42

open RACert RACert.Problem

theorem cover18367 : P.CoversSplit 24 10 18367 0xfffffffffa000000fffffffffa000000ffffffff00000000ffff000000000000cccccccc88000000ffccffccaa000000cccccccc00000000ffcc000000000000fffffffffa000000fffffffffa000000ffffffff0a000000ffff000000000000cccccccc88000000ffccffccaa00000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 860, 872, 915, 916, 1202, 1210, 1217, 1251, 1308, 1601]) (ps := [(14, [958], [1217])]) (by decide +kernel)

theorem c18367_0 : P.sumLeaves 24 18807808 409 = 7860550 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 18367) (lo := 0) (len := 409) (W := 7860550) check rows elimOK (by decide) (by decide) cover18367 (by decide)
  decide +kernel

theorem c18367_1 : P.sumLeaves 24 18808217 217 = 37344484 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 18367) (lo := 409) (len := 217) (W := 37344484) check rows elimOK (by decide) (by decide) cover18367 (by decide)
  decide +kernel

theorem c18367_2 : P.sumLeaves 24 18808434 264 = 42228176 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 18367) (lo := 626) (len := 264) (W := 42228176) check rows elimOK (by decide) (by decide) cover18367 (by decide)
  decide +kernel

theorem c18367_3 : P.sumLeaves 24 18808698 134 = 92956898 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 18367) (lo := 890) (len := 134) (W := 92956898) check rows elimOK (by decide) (by decide) cover18367 (by decide)
  decide +kernel

theorem h18367 : P.leaf 34 18367 = 180390108 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(409, 7860550), (217, 37344484), (264, 42228176), (134, 92956898)]) (.cons c18367_0 (.cons c18367_1 (.cons c18367_2 (.cons c18367_3 (.nil))))) (by decide) (by decide))

theorem h7159 : P.leaf 34 7159 = 180390108 :=
  orient4 (v := 18367) (by decide) (by decide +kernel) h18367

theorem cover7164 : P.CoversSplit 24 10 7164 0xffffffffaaaaaaaaffffffffaaaaaaaaf0f0f5f500000000f0f0f5f500000000cccccccc88888888cccccccc88888888c0c0c4c400000000c0c0c4c400000000ff00ff00aa00aa00ff33ff33aa22aa22f000f50000000000f030f531000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 859, 879, 916, 1202, 1259, 1601]) (by decide +kernel)

noncomputable def f7164 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (7335936 + i)

theorem c7164_0 : rowSum f7164 0 702 = 32299717 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 7164) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover7164 (by decide)
  decide +kernel

theorem c7164_1 : rowSum f7164 702 322 = 51665322 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 7164) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover7164 (by decide)
  decide +kernel

theorem sum7164 : rowSum f7164 0 1024 = 83965039 :=
  rowSum_append (F := f7164) (lo := 0) (n := 702) (m := 322) (A := 32299717) (B := 51665322) c7164_0 (c7164_1)

theorem h7164 : P.leaf 34 7164 = 83965039 :=
  leaf_weighted (k := 24) (d := 10) (H := 7164) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 7164) (by decide) (by decide +kernel)) sum7164

theorem cover7165 : P.CoversSplit 24 10 7165 0xffffffffafafaaaaffffffffafafaaaaffffffff00000000ffffffff00000000ccffccff88888888cccccccc88888888ccffccff00000000cccccccc00000000ff00ff00af00aa00ff33ff33af23aa22ff00ff0000000000ff33ff33000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 859, 879, 916, 1202, 1209, 1258, 1259, 1601]) (by decide +kernel)

theorem c7165_0 : P.sumLeaves 24 7336960 495 = 27525080 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7165) (lo := 0) (len := 495) (W := 27525080) check rows elimOK (by decide) (by decide) cover7165 (by decide)
  decide +kernel

theorem c7165_1 : P.sumLeaves 24 7337455 260 = 31461295 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7165) (lo := 495) (len := 260) (W := 31461295) check rows elimOK (by decide) (by decide) cover7165 (by decide)
  decide +kernel

theorem c7165_2 : P.sumLeaves 24 7337715 176 = 46619564 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7165) (lo := 755) (len := 176) (W := 46619564) check rows elimOK (by decide) (by decide) cover7165 (by decide)
  decide +kernel

theorem c7165_3 : P.sumLeaves 24 7337891 93 = 97590890 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7165) (lo := 931) (len := 93) (W := 97590890) check rows elimOK (by decide) (by decide) cover7165 (by decide)
  decide +kernel

theorem h7165 : P.leaf 34 7165 = 203196829 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(495, 27525080), (260, 31461295), (176, 46619564), (93, 97590890)]) (.cons c7165_0 (.cons c7165_1 (.cons c7165_2 (.cons c7165_3 (.nil))))) (by decide) (by decide))

theorem cover7167 : P.CoversSplit 24 10 7167 0xffffffffafafaaaaffffffffafafaaaaffffffffafafaaaaffffffffafafaaaaccffccff88888888cccccccc88888888ccffccff88888888cccccccc88888888ffffffffafafaaaaffffffffafafaaaaffffffffaaaaaaaaffffffffaaaaaaaaccffccff88888888cccccccc88888888cccccccc88888888cccccccc88888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [859, 916, 1202, 1209, 1217, 1258, 1259, 1601, 1609]) (by decide +kernel)

noncomputable def f7167 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (7339008 + i)

theorem c7167_0 : rowSum f7167 0 254 = 80324810 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 7167) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover7167 (by decide)
  decide +kernel

theorem c7167_1 : rowSum f7167 254 207 = 138348656 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 7167) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover7167 (by decide)
  decide +kernel

theorem c7167_2 : rowSum f7167 461 467 = 273706107 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 7167) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover7167 (by decide)
  decide +kernel

theorem c7167_3 : rowSum f7167 928 96 = 201589796 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 7167) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover7167 (by decide)
  decide +kernel

theorem sum7167 : rowSum f7167 0 1024 = 693969369 :=
  rowSum_append (F := f7167) (lo := 0) (n := 254) (m := 770) (A := 80324810) (B := 613644559) c7167_0 (rowSum_append (F := f7167) (lo := 254) (n := 207) (m := 563) (A := 138348656) (B := 475295903) c7167_1 (rowSum_append (F := f7167) (lo := 461) (n := 467) (m := 96) (A := 273706107) (B := 201589796) c7167_2 (c7167_3)))

theorem h7167 : P.leaf 34 7167 = 693969369 :=
  leaf_weighted (k := 24) (d := 10) (H := 7167) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 7167) (by decide) (by decide +kernel)) sum7167

theorem cover7396 : P.CoversSplit 24 10 7396 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h7396 : P.leaf 34 7396 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7396) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7396) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover7396 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7397 : P.CoversSplit 24 10 7397 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 573, 858, 865, 1209, 1258, 1272]) (by decide +kernel)

theorem h7397 : P.leaf 34 7397 = 73600 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7397) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7397) (weight := fun _ => 1) (xs := [511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover7397 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7398 : P.CoversSplit 24 10 7398 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 522, 524, 566, 573, 858, 865, 1209, 1258, 1272]) (by decide +kernel)

theorem h7398 : P.leaf 34 7398 = 378448 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7398) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7398) (weight := fun _ => 1) (xs := [511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover7398 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7399 : P.CoversSplit 24 10 7399 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 524, 566, 573, 858, 865, 1209, 1217, 1258, 1272, 1651]) (by decide +kernel)

theorem h7399 : P.leaf 34 7399 = 682184 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7399) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7399) (weight := fun _ => 1) (xs := [511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover7399 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7404 : P.CoversSplit 24 10 7404 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h7404 : P.leaf 34 7404 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7404) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7404) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover7404 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7405 : P.CoversSplit 24 10 7405 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 573, 858, 865, 1209, 1258, 1272]) (by decide +kernel)

theorem h7405 : P.leaf 34 7405 = 424314 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7405) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7405) (weight := fun _ => 1) (xs := [511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover7405 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7406 : P.CoversSplit 24 10 7406 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 522, 524, 566, 573, 858, 865, 1209, 1258, 1272]) (by decide +kernel)

theorem h7406 : P.leaf 34 7406 = 922784 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7406) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7406) (weight := fun _ => 1) (xs := [511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover7406 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7407 : P.CoversSplit 24 10 7407 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 524, 566, 573, 858, 865, 1209, 1217, 1258, 1272, 1651]) (by decide +kernel)

theorem h7407 : P.leaf 34 7407 = 1104842 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7407) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7407) (weight := fun _ => 1) (xs := [511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover7407 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover36652 : P.CoversSplit 24 10 36652 0x8800880080000000880088008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 472, 473, 517, 522, 529, 572, 915, 1202, 1209, 1258]) (ps := [(14, [923], [1272])]) (by decide +kernel)

theorem h36652 : P.leaf 34 36652 = 257264 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 36652) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 36652) (weight := fun _ => 1) (xs := [927, 939, 943, 955, 959, 991, 1003, 1007, 1019, 1023]) check rows elimOK (by decide) (by decide) cover36652 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h7412 : P.leaf 34 7412 = 257264 :=
  orient5 (v := 36652) (by decide) (by decide +kernel) h36652

theorem cover19631 : P.CoversSplit 24 10 19631 0xaa000000aa0000000000000000000000aa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000880000000000000000000000880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 573, 865, 916, 921, 1202, 1210]) (by decide +kernel)

theorem h19631 : P.leaf 34 19631 = 1327752 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 19631) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 19631) (weight := fun _ => 1) (xs := [379, 383, 475, 479, 507, 511, 889, 891, 893, 895, 985, 987, 989, 991, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover19631 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h7413 : P.leaf 34 7413 = 1327752 :=
  orient4 (v := 19631) (by decide) (by decide +kernel) h19631

theorem cover7414 : P.CoversSplit 24 10 7414 0xf0f00000f0f500000000000000000000f0f00000f0f5000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 573, 858, 865, 866, 908, 916, 1210, 1217, 1259, 1264, 1308]) (by decide +kernel)

theorem c7414_0 : P.sumLeaves 24 7591936 1024 = 6026177 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7414) (lo := 0) (len := 1024) (W := 6026177) check rows elimOK (by decide) (by decide) cover7414 (by decide)
  decide +kernel

theorem h7414 : P.leaf 34 7414 = 6026177 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6026177)]) (.cons c7414_0 (.nil)) (by decide) (by decide))

theorem cover36669 : P.CoversSplit 24 10 36669 0xff00ff00f0000000ff00ff00f0000000ff00ff0000000000ff00ff00000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 517, 529, 572, 915, 921, 1202, 1209, 1258]) (ps := [(14, [923], [1272])]) (by decide +kernel)

theorem c36669_0 : P.sumLeaves 24 37549056 1024 = 21974908 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 36669) (lo := 0) (len := 1024) (W := 21974908) check rows elimOK (by decide) (by decide) cover36669 (by decide)
  decide +kernel

theorem h36669 : P.leaf 34 36669 = 21974908 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 21974908)]) (.cons c36669_0 (.nil)) (by decide) (by decide))

theorem h7415 : P.leaf 34 7415 = 21974908 :=
  orient5 (v := 36669) (by decide) (by decide +kernel) h36669

theorem cover36684 : P.CoversSplit 24 10 36684 0x8800000088000000880000008800000088000000080000008800000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 472, 473, 515, 516, 522, 523, 565, 572, 915, 1202, 1209]) (by decide +kernel)

theorem h36684 : P.leaf 34 36684 = 637456 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 36684) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 36684) (weight := fun _ => 1) (xs := [795, 827, 831, 859, 891, 895, 923, 927, 955, 959, 987, 991, 1019, 1023]) check rows elimOK (by decide) (by decide) cover36684 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h7416 : P.leaf 34 7416 = 637456 :=
  orient5 (v := 36684) (by decide) (by decide +kernel) h36684

def seg : List (ℕ × ℕ) := [(7159, 48), (7164, 24), (7165, 48), (7167, 24), (7396, 48), (7397, 48), (7398, 48), (7399, 48), (7404, 24), (7405, 24), (7406, 24), (7407, 24), (7412, 48), (7413, 48), (7414, 48), (7415, 48), (7416, 48)]

theorem segOK : checkSeg 16 perms 7159 7417 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 7159 7417 672 38646619200 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 38646619200)
    (SegSum.cons (w := 48) h7159 (SegSum.cons (w := 24) h7164 (SegSum.cons (w := 48) h7165 (SegSum.cons (w := 24) h7167 (SegSum.cons (w := 48) h7396 (SegSum.cons (w := 48) h7397 (SegSum.cons (w := 48) h7398 (SegSum.cons (w := 48) h7399 (SegSum.cons (w := 24) h7404 (SegSum.cons (w := 24) h7405 (SegSum.cons (w := 24) h7406 (SegSum.cons (w := 24) h7407 (SegSum.cons (w := 48) h7412 (SegSum.cons (w := 48) h7413 (SegSum.cons (w := 48) h7414 (SegSum.cons (w := 48) h7415 (SegSum.cons (w := 48) h7416 (show SegSum (P.leaf 34) [] 0 from rfl)))))))))))))))))) (by decide)

end RACert.S4N1.C0.S42
