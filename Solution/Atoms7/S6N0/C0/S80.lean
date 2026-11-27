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

namespace RACert.S6N0.C0.S80

open RACert RACert.Problem

theorem cover119623 : P.CoversSplit 26 10 119623 0xa0a00000a0a000000000000000000000a0a00000a0a0000000000000000000000505050505050505050505050505050505050505050500000505050500000000a0a00000a0a000000000000000000000a0a000000000000000000000000000000505050505050505050505050505050505050505000000000505050500000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 579, 873, 1273, 1315, 1322, 1665]) (by decide +kernel)

noncomputable def f119623 (i : ℕ) := rowWeight keep9 twice9 i * P.leaf 26 (122493952 + i)

theorem c119623_0 : rowSum f119623 0 1024 = 1176055 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 119623) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover119623 (by decide)
  decide +kernel

theorem sum119623 : rowSum f119623 0 1024 = 1176055 :=
  c119623_0

theorem h119623 : P.leaf 36 119623 = 1176055 :=
  leaf_weighted (k := 26) (d := 10) (H := 119623) (keep := keep9) (twice := twice9) rows (by decide) (by decide) bal9 (invRow9 (H := 119623) (by decide) (by decide +kernel)) sum119623

theorem cover119631 : P.CoversSplit 26 10 119631 0xa0a00000a0a000000000000000000000a0a00000a0a0000000000000000000000505050505050505050505050505050505050505050500000505050500000000a0a00000a0a000000000000000000000a0a000000000000000000000000000000505050505050505050505050505050505050505000000000505050500000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 579, 873, 1273, 1315, 1322, 1665]) (by decide +kernel)

noncomputable def f119631 (i : ℕ) := rowWeight keep9 twice9 i * P.leaf 26 (122502144 + i)

theorem c119631_0 : rowSum f119631 0 1024 = 3670795 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 119631) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover119631 (by decide)
  decide +kernel

theorem sum119631 : rowSum f119631 0 1024 = 3670795 :=
  c119631_0

theorem h119631 : P.leaf 36 119631 = 3670795 :=
  leaf_weighted (k := 26) (d := 10) (H := 119631) (keep := keep9) (twice := twice9) rows (by decide) (by decide) bal9 (invRow9 (H := 119631) (by decide) (by decide +kernel)) sum119631

theorem cover119639 : P.CoversSplit 26 10 119639 0xa0a00000a0a000000000000000000000a0a00000a0a0000000000000000000000000000000000000000005050000050500000000000000000000050500000000a0a00000a0a000000000000000000000a0a000000000000000000000000000000000000000000000000005050000050500000000000000000000050500000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 579, 873, 1273, 1315, 1322]) (by decide +kernel)

noncomputable def f119639 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (122510336 + i)

theorem c119639_0 : rowSum f119639 0 1024 = 7497540 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 119639) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover119639 (by decide)
  decide +kernel

theorem sum119639 : rowSum f119639 0 1024 = 7497540 :=
  c119639_0

theorem h119639 : P.leaf 36 119639 = 7497540 :=
  leaf_weighted (k := 26) (d := 10) (H := 119639) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 119639) (by decide) (by decide +kernel)) sum119639

theorem cover119647 : P.CoversSplit 26 10 119647 0xa0a00000a0a000000000000000000000a0a00000a0a0000000000000000000000000000000000000000005050000050500000000000000000000050500000000a0a00000a0a000000000000000000000a0a000000000000000000000000000000000000000000000000005050000050500000000000000000000050500000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 579, 873, 1273, 1315, 1322]) (by decide +kernel)

noncomputable def f119647 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (122518528 + i)

theorem c119647_0 : rowSum f119647 0 1024 = 7920556 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 119647) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover119647 (by decide)
  decide +kernel

theorem sum119647 : rowSum f119647 0 1024 = 7920556 :=
  c119647_0

theorem h119647 : P.leaf 36 119647 = 7920556 :=
  leaf_weighted (k := 26) (d := 10) (H := 119647) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 119647) (by decide) (by decide +kernel)) sum119647

theorem cover119671 : P.CoversSplit 26 10 119671 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0c0c000000000000000000505000005050000050500000505000005050000050500000505000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f00000000000000000000000000505000005050000050500000505000005050000000000000505000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 873, 922, 1273, 1322, 1658, 1665]) (by decide +kernel)

theorem c119671_0 : P.sumLeaves 26 122543104 752 = 16691826 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 119671) (lo := 0) (len := 752) (W := 16691826) check rows elimOK (by decide) (by decide) cover119671 (by decide)
  decide +kernel

theorem c119671_1 : P.sumLeaves 26 122543856 272 = 25197006 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 119671) (lo := 752) (len := 272) (W := 25197006) check rows elimOK (by decide) (by decide) cover119671 (by decide)
  decide +kernel

theorem h119671 : P.leaf 36 119671 = 41888832 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(752, 16691826), (272, 25197006)]) (.cons c119671_0 (.cons c119671_1 (.nil))) (by decide) (by decide))

theorem cover119679 : P.CoversSplit 26 10 119679 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0c0c000000000000000000505000005050000050500000505000005050000050500000505000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f00000000000000000000000000505000005050000050500000505000005050000000000000505000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 873, 922, 1273, 1322, 1658, 1665]) (by decide +kernel)

theorem c119679_0 : P.sumLeaves 26 122551296 752 = 21269378 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 119679) (lo := 0) (len := 752) (W := 21269378) check rows elimOK (by decide) (by decide) cover119679 (by decide)
  decide +kernel

theorem c119679_1 : P.sumLeaves 26 122552048 272 = 26899230 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 119679) (lo := 752) (len := 272) (W := 26899230) check rows elimOK (by decide) (by decide) cover119679 (by decide)
  decide +kernel

theorem h119679 : P.leaf 36 119679 = 48168608 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(752, 21269378), (272, 26899230)]) (.cons c119679_0 (.cons c119679_1 (.nil))) (by decide) (by decide))

theorem cover119799 : P.CoversSplit 26 10 119799 0xfffffffffffffafafffffffffffffafaffffffffffffc8c8fafafafac8c8c8c8fffffafafffffafafafafafafafafafafffffafaffffc8c8fafafafac8c8c8c8fffffffffffffafafffffffffffffafaffffffffccccc8c8fafafafac8c8c8c8fffffafafffffafafafafafafafafafafffffafaccccc8c8fafafafac8c8c8c8 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 873, 922, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f119799 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (122674176 + i)

theorem c119799_0 : rowSum f119799 0 240 = 129199295 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 119799) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover119799 (by decide)
  decide +kernel

theorem c119799_1 : rowSum f119799 240 180 = 306210162 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 119799) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover119799 (by decide)
  decide +kernel

theorem c119799_2 : rowSum f119799 420 189 = 373415318 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 119799) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover119799 (by decide)
  decide +kernel

theorem c119799_3 : rowSum f119799 609 213 = 425948673 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 119799) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover119799 (by decide)
  decide +kernel

theorem c119799_4 : rowSum f119799 822 194 = 513821154 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 119799) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover119799 (by decide)
  decide +kernel

theorem c119799_5 : rowSum f119799 1016 8 = 70181364 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 119799) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover119799 (by decide)
  decide +kernel

theorem sum119799 : rowSum f119799 0 1024 = 1818775966 :=
  rowSum_append (F := f119799) (lo := 0) (n := 240) (m := 784) (A := 129199295) (B := 1689576671) c119799_0 (rowSum_append (F := f119799) (lo := 240) (n := 180) (m := 604) (A := 306210162) (B := 1383366509) c119799_1 (rowSum_append (F := f119799) (lo := 420) (n := 189) (m := 415) (A := 373415318) (B := 1009951191) c119799_2 (rowSum_append (F := f119799) (lo := 609) (n := 213) (m := 202) (A := 425948673) (B := 584002518) c119799_3 (rowSum_append (F := f119799) (lo := 822) (n := 194) (m := 8) (A := 513821154) (B := 70181364) c119799_4 (c119799_5)))))

theorem h119799 : P.leaf 36 119799 = 1818775966 :=
  leaf_weighted (k := 26) (d := 10) (H := 119799) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 119799) (by decide) (by decide +kernel)) sum119799

theorem cover119807 : P.CoversSplit 26 10 119807 0xfffffffffffffafafffffffffffffafaffffffffffffc8c8fafafafac8c8c8c8fffffafafffffafafafafafafafafafafffffafaffffc8c8fafafafac8c8c8c8fffffffffffffafafffffffffffffafaffffffffccccc8c8fafafafac8c8c8c8fffffafafffffafafafafafafafafafafffffafaccccc8c8fafafafac8c8c8c8 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 922, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f119807 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (122682368 + i)

theorem c119807_0 : rowSum f119807 0 240 = 615075256 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 119807) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover119807 (by decide)
  decide +kernel

theorem c119807_1 : rowSum f119807 240 180 = 850844071 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 119807) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover119807 (by decide)
  decide +kernel

theorem c119807_2 : rowSum f119807 420 189 = 948077744 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 119807) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover119807 (by decide)
  decide +kernel

theorem c119807_3 : rowSum f119807 609 213 = 1140658232 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 119807) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover119807 (by decide)
  decide +kernel

theorem c119807_4 : rowSum f119807 822 194 = 1300286244 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 119807) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover119807 (by decide)
  decide +kernel

theorem c119807_5 : rowSum f119807 1016 8 = 119884488 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 119807) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover119807 (by decide)
  decide +kernel

theorem sum119807 : rowSum f119807 0 1024 = 4974826035 :=
  rowSum_append (F := f119807) (lo := 0) (n := 240) (m := 784) (A := 615075256) (B := 4359750779) c119807_0 (rowSum_append (F := f119807) (lo := 240) (n := 180) (m := 604) (A := 850844071) (B := 3508906708) c119807_1 (rowSum_append (F := f119807) (lo := 420) (n := 189) (m := 415) (A := 948077744) (B := 2560828964) c119807_2 (rowSum_append (F := f119807) (lo := 609) (n := 213) (m := 202) (A := 1140658232) (B := 1420170732) c119807_3 (rowSum_append (F := f119807) (lo := 822) (n := 194) (m := 8) (A := 1300286244) (B := 119884488) c119807_4 (c119807_5)))))

theorem h119807 : P.leaf 36 119807 = 4974826035 :=
  leaf_weighted (k := 26) (d := 10) (H := 119807) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 119807) (by decide) (by decide +kernel)) sum119807

def seg : List (ℕ × ℕ) := [(119623, 20), (119631, 20), (119639, 180), (119647, 180), (119671, 180), (119679, 180), (119799, 60), (119807, 60)]

theorem segOK : checkSeg 20 perms 119623 120663 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 119623 120663 880 426698653540 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 426698653540)
    (SegSum.cons (w := 20) h119623 (SegSum.cons (w := 20) h119631 (SegSum.cons (w := 180) h119639 (SegSum.cons (w := 180) h119647 (SegSum.cons (w := 180) h119671 (SegSum.cons (w := 180) h119679 (SegSum.cons (w := 60) h119799 (SegSum.cons (w := 60) h119807 (show SegSum (P.leaf 36) [] 0 from rfl))))))))) (by decide)

end RACert.S6N0.C0.S80
