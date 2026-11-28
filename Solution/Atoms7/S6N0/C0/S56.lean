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

namespace RACert.S6N0.C0.S56

open RACert RACert.Problem

theorem cover89086 : P.CoversSplit 26 10 89086 0xfffffffffffcfaf8fffffffafffcfaf8fffffffffffcfac8fafafafac8c8c8c8fffffafafffcfaf8fafafafafaf8faf8fffffafafffcfac8fafafafac8c8c8c8ffffffffffccfac8fffffffaffccfac8ffffffffccccc8c8fafafafac8c8c8c80000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [874, 922, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f89086 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (91224064 + i)

theorem c89086_0 : rowSum f89086 0 409 = 167064086 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 89086) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover89086 (by decide)
  decide +kernel

theorem c89086_1 : rowSum f89086 409 381 = 416470902 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 89086) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover89086 (by decide)
  decide +kernel

theorem c89086_2 : rowSum f89086 790 215 = 508868275 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 89086) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover89086 (by decide)
  decide +kernel

theorem c89086_3 : rowSum f89086 1005 19 = 107892396 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 89086) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover89086 (by decide)
  decide +kernel

theorem sum89086 : rowSum f89086 0 1024 = 1200295659 :=
  rowSum_append (F := f89086) (lo := 0) (n := 409) (m := 615) (A := 167064086) (B := 1033231573) c89086_0 (rowSum_append (F := f89086) (lo := 409) (n := 381) (m := 234) (A := 416470902) (B := 616760671) c89086_1 (rowSum_append (F := f89086) (lo := 790) (n := 215) (m := 19) (A := 508868275) (B := 107892396) c89086_2 (c89086_3)))

theorem h89086 : P.leaf 36 89086 = 1200295659 :=
  leaf_weighted (k := 26) (d := 10) (H := 89086) (keep := keep4) (twice := twice4) rows (by decide) (by decide) (bal4) (invRow4 (H := 89086) (by decide) (by decide +kernel)) sum89086

theorem cover799743 : P.CoversSplit 26 10 799743 0xfffffffafffffffaffffaaaaffffaaaafffcfff8ccccccc8fffcaaa8cccc8888fffffafafffffafaffffaaaaffffaaaafffcfaf8ccccc8c8fffcaaa8cccc8888fffffffafffffffaffffaaaaffffaaaaffccffc8ccccccc8ffccaa88cccc8888fffffafafffffafaffffaaaaffffaaaaffccfac8ccccc8c8ffccaa88cccc8888 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 930, 972, 979, 1265, 1273]) (by decide +kernel)

noncomputable def f799743 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 26 (818936832 + i)

theorem c799743_0 : rowSum f799743 0 275 = 765657602 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 799743) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover799743 (by decide)
  decide +kernel

theorem c799743_1 : rowSum f799743 275 158 = 918916136 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 799743) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover799743 (by decide)
  decide +kernel

theorem c799743_2 : rowSum f799743 433 388 = 1061226218 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 799743) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover799743 (by decide)
  decide +kernel

theorem c799743_3 : rowSum f799743 821 203 = 873835066 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 799743) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover799743 (by decide)
  decide +kernel

theorem sum799743 : rowSum f799743 0 1024 = 3619635022 :=
  rowSum_append (F := f799743) (lo := 0) (n := 275) (m := 749) (A := 765657602) (B := 2853977420) c799743_0 (rowSum_append (F := f799743) (lo := 275) (n := 158) (m := 591) (A := 918916136) (B := 1935061284) c799743_1 (rowSum_append (F := f799743) (lo := 433) (n := 388) (m := 203) (A := 1061226218) (B := 873835066) c799743_2 (c799743_3)))

theorem h799743 : P.leaf 36 799743 = 3619635022 :=
  leaf_weighted (k := 26) (d := 10) (H := 799743) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 799743) (by decide) (by decide +kernel)) sum799743

theorem h89087 : P.leaf 36 89087 = 3619635022 :=
  orient324 (v := 799743) (by decide) (by decide +kernel) h799743

theorem cover89559 : P.CoversSplit 26 10 89559 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 531, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h89559 : P.leaf 36 89559 = 5504977 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 89559) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 89559) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover89559 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover89564 : P.CoversSplit 26 10 89564 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 922, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h89564 : P.leaf 36 89564 = 4869108 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 89564) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 89564) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover89564 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover89565 : P.CoversSplit 26 10 89565 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 922, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h89565 : P.leaf 36 89565 = 6104773 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 89565) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 89565) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover89565 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover89567 : P.CoversSplit 26 10 89567 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h89567 : P.leaf 36 89567 = 8011129 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 89567) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 89567) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover89567 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover89580 : P.CoversSplit 26 10 89580 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h89580 : P.leaf 36 89580 = 7114308 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 89580) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 89580) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover89580 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover89581 : P.CoversSplit 26 10 89581 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h89581 : P.leaf 36 89581 = 7246938 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 89581) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 89581) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover89581 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover89582 : P.CoversSplit 26 10 89582 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h89582 : P.leaf 36 89582 = 8130078 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 89582) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 89582) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover89582 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover89583 : P.CoversSplit 26 10 89583 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h89583 : P.leaf 36 89583 = 8439249 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 89583) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 89583) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover89583 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover89598 : P.CoversSplit 26 10 89598 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h89598 : P.leaf 36 89598 = 10934084 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 89598) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 89598) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover89598 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover89599 : P.CoversSplit 26 10 89599 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h89599 : P.leaf 36 89599 = 11570142 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 89599) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 89599) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover89599 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover89726 : P.CoversSplit 26 10 89726 0xfffffffffffcfaf800000000000000000000000000000000000000000f0c0a080f0f0a0a0f0c0a080f0f0a0a0f0c0a080000000000000000000000000f0c0a0800000000ffccfac8000000000000000000000000ffccfac8000000000f0c0a080000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 587, 874, 979, 1315, 1658, 1665]) (by decide +kernel)

noncomputable def f89726 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (91879424 + i)

theorem c89726_0 : rowSum f89726 0 1024 = 40706472 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 89726) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover89726 (by decide)
  decide +kernel

theorem sum89726 : rowSum f89726 0 1024 = 40706472 :=
  c89726_0

theorem h89726 : P.leaf 36 89726 = 40706472 :=
  leaf_weighted (k := 26) (d := 10) (H := 89726) (keep := keep4) (twice := twice4) rows (by decide) (by decide) (bal4) (invRow4 (H := 89726) (by decide) (by decide +kernel)) sum89726

theorem cover89727 : P.CoversSplit 26 10 89727 0xfffffffffffcfaf800000000000000000000000000000000000000000f0c0a080f0f0a0a0f0c0a080f0f0a0a0f0c0a080000000000000000000000000f0c0a0800000000ffccfac8000000000000000000000000ffccfac8000000000f0c0a08000000000f0c0a08000000000f0c0a08000000000f0c0a08000000000f0c0a08 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 587, 979, 1315, 1658, 1665]) (by decide +kernel)

noncomputable def f89727 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (91880448 + i)

theorem c89727_0 : rowSum f89727 0 988 = 48844996 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 89727) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover89727 (by decide)
  decide +kernel

theorem c89727_1 : rowSum f89727 988 36 = 24389200 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 89727) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover89727 (by decide)
  decide +kernel

theorem sum89727 : rowSum f89727 0 1024 = 73234196 :=
  rowSum_append (F := f89727) (lo := 0) (n := 988) (m := 36) (A := 48844996) (B := 24389200) c89727_0 (c89727_1)

theorem h89727 : P.leaf 36 89727 = 73234196 :=
  leaf_weighted (k := 26) (d := 10) (H := 89727) (keep := keep4) (twice := twice4) rows (by decide) (by decide) (bal4) (invRow4 (H := 89727) (by decide) (by decide +kernel)) sum89727

theorem cover306585 : P.CoversSplit 26 10 306585 0x8888000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 537, 538, 629, 636, 930, 1266, 1272, 1665]) (by decide +kernel)

theorem h306585 : P.leaf 36 306585 = 694112 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 306585) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 306585) (weight := fun _ => 1) (xs := [1011, 1015, 1019, 1023]) check rows elimOK (by decide) (by decide) cover306585 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h89812 : P.leaf 36 89812 = 694112 :=
  orient84 (v := 306585) (by decide) (by decide +kernel) h306585

theorem cover105955 : P.CoversSplit 26 10 105955 0x8800880088008800000000000000000000000000000000000000000000000000000000000000000000004000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 629, 636, 930, 965, 1658]) (by decide +kernel)

theorem h105955 : P.leaf 36 105955 = 6571223 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 105955) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 105955) (weight := fun _ => 1) (xs := [654, 686, 971, 975, 987, 991, 1003, 1007, 1019, 1023]) check rows elimOK (by decide) (by decide) cover105955 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h89813 : P.leaf 36 89813 = 6571223 :=
  orient4 (v := 105955) (by decide) (by decide +kernel) h105955

theorem cover105958 : P.CoversSplit 26 10 105958 0xcc00cc00cc00c800000000000000000000000000000000000000000000110000440040004400400044000000440000000000000000000000000000000011000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 531, 629, 636, 922, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c105958_0 : P.sumLeaves 26 108500992 704 = 628717 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 105958) (lo := 0) (len := 704) (W := 628717) check rows elimOK (by decide) (by decide) cover105958 (by decide)
  decide +kernel

theorem contract105958_1 : P.leaf 32 1695339 = 0 := by
  exact leaf_contract_zero (ss := [(7, 1, 482), (29, 1, 636), (11, 1, 923), (31, 1, 930), (21, 0, 1658), (2, 1, 475), (5, 1, 586), (9, 0, 1259), (15, 0, 1259)]) (q := 1609) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c105958_1 : P.sumLeaves 26 108501696 64 = 0 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1695339) rows (by decide) (by decide)).symm.trans contract105958_1

theorem c105958_2 : P.sumLeaves 26 108501760 256 = 12909272 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 105958) (lo := 768) (len := 256) (W := 12909272) check rows elimOK (by decide) (by decide) cover105958 (by decide)
  decide +kernel

theorem h105958 : P.leaf 36 105958 = 13537989 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(704, 628717), (64, 0), (256, 12909272)]) (.cons c105958_0 (.cons c105958_1 (.cons c105958_2 (.nil)))) (by decide) (by decide))

theorem h89814 : P.leaf 36 89814 = 13537989 :=
  orient4 (v := 105958) (by decide) (by decide +kernel) h105958

theorem cover105959 : P.CoversSplit 26 10 105959 0xcc00cc00cc00c800000000000000000000000000000000000000000000110000440040004400400044000000440000000000000000000000000000000011000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 629, 636, 922, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c105959_0 : P.sumLeaves 26 108502016 704 = 1137123 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 105959) (lo := 0) (len := 704) (W := 1137123) check rows elimOK (by decide) (by decide) cover105959 (by decide)
  decide +kernel

theorem contract105959_1 : P.leaf 32 1695355 = 0 := by
  exact leaf_contract_zero (ss := [(7, 1, 482), (29, 1, 636), (11, 1, 923), (31, 1, 930), (21, 0, 1658), (2, 1, 475), (5, 1, 586), (9, 0, 1259), (15, 0, 1259)]) (q := 1609) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c105959_1 : P.sumLeaves 26 108502720 64 = 0 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1695355) rows (by decide) (by decide)).symm.trans contract105959_1

theorem c105959_2 : P.sumLeaves 26 108502784 256 = 27135450 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 105959) (lo := 768) (len := 256) (W := 27135450) check rows elimOK (by decide) (by decide) cover105959 (by decide)
  decide +kernel

theorem h105959 : P.leaf 36 105959 = 28272573 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(704, 1137123), (64, 0), (256, 27135450)]) (.cons c105959_0 (.cons c105959_1 (.cons c105959_2 (.nil)))) (by decide) (by decide))

theorem h89815 : P.leaf 36 89815 = 28272573 :=
  orient4 (v := 105959) (by decide) (by decide +kernel) h105959

theorem cover113123 : P.CoversSplit 26 10 113123 0x8800880088008800880088008800880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 629, 636, 930, 1266, 1273]) (by decide +kernel)

theorem h113123 : P.leaf 36 113123 = 7346364 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 113123) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 113123) (weight := fun _ => 1) (xs := [907, 911, 923, 927, 939, 943, 955, 959, 971, 975, 987, 991, 1003, 1007, 1019, 1023]) check rows elimOK (by decide) (by decide) cover113123 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h89818 : P.leaf 36 89818 = 7346364 :=
  orient86 (v := 113123) (by decide) (by decide +kernel) h113123

theorem cover89819 : P.CoversSplit 26 10 89819 0xa0a00000a0a00000a0a00000a0a0000000000000000000000000000020200000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000020000000000000002000000000000000200000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 587, 972, 979, 1315, 1665]) (by decide +kernel)

theorem h89819 : P.leaf 36 89819 = 27732640 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 89819) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 89819) (weight := fun _ => 1) (xs := [285, 349, 413, 477, 789, 797, 917, 919, 925, 927, 949, 951, 957, 959, 981, 983, 989, 991, 1013, 1015, 1021, 1023]) check rows elimOK (by decide) (by decide) cover89819 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover105962 : P.CoversSplit 26 10 105962 0xaaaaaaaaaaaaaaaa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000222222220000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 531, 629, 636, 922, 930, 965, 1658, 1665]) (by decide +kernel)

theorem c105962_0 : P.sumLeaves 26 108505088 1024 = 20914803 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 105962) (lo := 0) (len := 1024) (W := 20914803) check rows elimOK (by decide) (by decide) cover105962 (by decide)
  decide +kernel

theorem h105962 : P.leaf 36 105962 = 20914803 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 20914803)]) (.cons c105962_0 (.nil)) (by decide) (by decide))

theorem h89820 : P.leaf 36 89820 = 20914803 :=
  orient4 (v := 105962) (by decide) (by decide +kernel) h105962

theorem cover105963 : P.CoversSplit 26 10 105963 0xaaaaaaaaaaaaaaaa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000222222220000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 629, 636, 922, 930, 965, 1658, 1665]) (by decide +kernel)

theorem c105963_0 : P.sumLeaves 26 108506112 1024 = 48314406 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 105963) (lo := 0) (len := 1024) (W := 48314406) check rows elimOK (by decide) (by decide) cover105963 (by decide)
  decide +kernel

theorem h105963 : P.leaf 36 105963 = 48314406 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 48314406)]) (.cons c105963_0 (.nil)) (by decide) (by decide))

theorem h89821 : P.leaf 36 89821 = 48314406 :=
  orient4 (v := 105963) (by decide) (by decide +kernel) h105963

theorem cover89822 : P.CoversSplit 26 10 89822 0xffff0000fffc0504ffff0000fffc050000000000000000000000000030300000050505050504050400000000000000000000000000000000000000000000000000000000330001000000000033000100000000003300010000000000300000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 587, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89822_0 : P.sumLeaves 26 91977728 1020 = 60696676 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89822) (lo := 0) (len := 1020) (W := 60696676) check rows elimOK (by decide) (by decide) cover89822 (by decide)
  decide +kernel

theorem c89822_1 : P.sumLeaves 26 91978748 4 = 8192360 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89822) (lo := 1020) (len := 4) (W := 8192360) check rows elimOK (by decide) (by decide) cover89822 (by decide)
  decide +kernel

theorem h89822 : P.leaf 36 89822 = 68889036 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1020, 60696676), (4, 8192360)]) (.cons c89822_0 (.cons c89822_1 (.nil))) (by decide) (by decide))

theorem cover89823 : P.CoversSplit 26 10 89823 0xffff0000fffc0504ffff0000fffc050000000000000000000000000030300000050505050504050400000000000000000000000000000000000000000000000000000000330001000000000033000100000000003300010000000000300000000000000001000100000000000000000000000000010001000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 587, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89823_0 : P.sumLeaves 26 91978752 1016 = 114250005 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89823) (lo := 0) (len := 1016) (W := 114250005) check rows elimOK (by decide) (by decide) cover89823 (by decide)
  decide +kernel

theorem c89823_1 : P.sumLeaves 26 91979768 8 = 22929276 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89823) (lo := 1016) (len := 8) (W := 22929276) check rows elimOK (by decide) (by decide) cover89823 (by decide)
  decide +kernel

theorem h89823 : P.leaf 36 89823 = 137179281 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1016, 114250005), (8, 22929276)]) (.cons c89823_0 (.cons c89823_1 (.nil))) (by decide) (by decide))

theorem cover105939 : P.CoversSplit 26 10 105939 0x8000800080008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 530, 608, 629, 636, 930, 965, 1658]) (by decide +kernel)

theorem h105939 : P.leaf 36 105939 = 3146904 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 105939) (keep := keep16) (twice := twice16) rows (by decide) (by decide) bal16 (invRow16 (H := 105939) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 105939) (weight := rowWeight keep16 twice16) (xs := [975, 991, 1007, 1023]) check rows elimOK (by decide) (by decide) cover105939 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h89829 : P.leaf 36 89829 = 3146904 :=
  orient4 (v := 105939) (by decide) (by decide +kernel) h105939

theorem cover105942 : P.CoversSplit 26 10 105942 0xcc00cc00cc00c800000000000000000000000000000000000000000000110000000000000000000044000000440000000000000000000000000000000011000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [489, 530, 531, 629, 636, 922, 930, 1315, 1322, 1658, 1665]) (ps := [(21, [1272], [1658])]) (by decide +kernel)

theorem h105942 : P.leaf 36 105942 = 15411503 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 105942) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 105942) (weight := fun _ => 1) (xs := [528, 532, 666, 670, 698, 702, 784, 788, 971, 974, 975, 986, 987, 990, 991, 1002, 1003, 1006, 1007, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover105942 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h89830 : P.leaf 36 89830 = 15411503 :=
  orient4 (v := 105942) (by decide) (by decide +kernel) h105942

theorem cover105943 : P.CoversSplit 26 10 105943 0xcc00cc00cc00c800000000000000000000000000000000000000000000110000000000000000000044000000440000000000000000000000000000000011000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [489, 530, 629, 636, 922, 930, 1315, 1322, 1658, 1665]) (ps := [(21, [1272], [1658])]) (by decide +kernel)

theorem h105943 : P.leaf 36 105943 = 25516864 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 105943) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 105943) (weight := fun _ => 1) (xs := [528, 532, 666, 670, 698, 702, 784, 788, 971, 974, 975, 986, 987, 990, 991, 1002, 1003, 1006, 1007, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover105943 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h89831 : P.leaf 36 89831 = 25516864 :=
  orient4 (v := 105943) (by decide) (by decide +kernel) h105943

theorem cover89834 : P.CoversSplit 26 10 89834 0xf0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300030000000000030003000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 524, 874, 972, 979, 1266, 1665]) (by decide +kernel)

theorem c89834_0 : P.sumLeaves 26 91990016 1024 = 28594340 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89834) (lo := 0) (len := 1024) (W := 28594340) check rows elimOK (by decide) (by decide) cover89834 (by decide)
  decide +kernel

theorem h89834 : P.leaf 36 89834 = 28594340 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 28594340)]) (.cons c89834_0 (.nil)) (by decide) (by decide))

theorem cover89835 : P.CoversSplit 26 10 89835 0xf0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f000000000000000000000000030303000000000000000000000000000000000000000000000000000000000000000000000000000300030000000000030003000000000003000300000000000300030000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 587, 972, 979, 1266, 1322, 1658, 1665]) (by decide +kernel)

theorem c89835_0 : P.sumLeaves 26 91991040 1024 = 66533892 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89835) (lo := 0) (len := 1024) (W := 66533892) check rows elimOK (by decide) (by decide) cover89835 (by decide)
  decide +kernel

theorem h89835 : P.leaf 36 89835 = 66533892 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 66533892)]) (.cons c89835_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(89086, 360), (89087, 360), (89559, 90), (89564, 360), (89565, 720), (89567, 360), (89580, 360), (89581, 360), (89582, 720), (89583, 720), (89598, 360), (89599, 360), (89726, 120), (89727, 120), (89812, 720), (89813, 720), (89814, 720), (89815, 720), (89818, 720), (89819, 720), (89820, 720), (89821, 720), (89822, 720), (89823, 720), (89829, 360), (89830, 720), (89831, 720), (89834, 720), (89835, 720)]

theorem segOK : checkSeg 20 perms 89086 89836 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 89086 89836 15810 2141476564650 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 2141476564650)
    (SegSum.cons (w := 360) h89086 (SegSum.cons (w := 360) h89087 (SegSum.cons (w := 90) h89559 (SegSum.cons (w := 360) h89564 (SegSum.cons (w := 720) h89565 (SegSum.cons (w := 360) h89567 (SegSum.cons (w := 360) h89580 (SegSum.cons (w := 360) h89581 (SegSum.cons (w := 720) h89582 (SegSum.cons (w := 720) h89583 (SegSum.cons (w := 360) h89598 (SegSum.cons (w := 360) h89599 (SegSum.cons (w := 120) h89726 (SegSum.cons (w := 120) h89727 (SegSum.cons (w := 720) h89812 (SegSum.cons (w := 720) h89813 (SegSum.cons (w := 720) h89814 (SegSum.cons (w := 720) h89815 (SegSum.cons (w := 720) h89818 (SegSum.cons (w := 720) h89819 (SegSum.cons (w := 720) h89820 (SegSum.cons (w := 720) h89821 (SegSum.cons (w := 720) h89822 (SegSum.cons (w := 720) h89823 (SegSum.cons (w := 360) h89829 (SegSum.cons (w := 720) h89830 (SegSum.cons (w := 720) h89831 (SegSum.cons (w := 720) h89834 (SegSum.cons (w := 720) h89835 (show SegSum (P.leaf 36) [] 0 from rfl)))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S56
