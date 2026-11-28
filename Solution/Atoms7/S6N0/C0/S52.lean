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

namespace RACert.S6N0.C0.S52

open RACert RACert.Problem

theorem cover302995 : P.CoversSplit 26 10 302995 0xf000040000200000000000000000000000000000000000000000000000000000f000040000200000000000000000000000000000000000000000000000000000f000040000200000000000000000000000000000000000000000000000000000f000040000200000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 482, 488, 489, 531, 537, 922, 923, 929, 930, 1265, 1273]) (by decide +kernel)

theorem h302995 : P.leaf 36 302995 = 12368504 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 302995) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 302995) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 302995) (weight := rowWeight keep0 twice0) (xs := [213, 234, 252, 253, 254, 255, 469, 490, 508, 509, 510, 511, 725, 746, 764, 765, 766, 767, 981, 1002, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover302995 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h81865 : P.leaf 36 81865 = 12368504 :=
  orient6 (v := 302995) (by decide) (by decide +kernel) h302995

theorem cover309715 : P.CoversSplit 26 10 309715 0xaa000000aa000000aa000000aa00000000000000000000000000000000000000000000000000000000000a0000000a000000000000000000000000000000000000220000002200000022000000220000000000000000000000000000000000000000000000000000000000020000000200000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 488, 489, 530, 629, 636, 930, 1665]) (by decide +kernel)

theorem h309715 : P.leaf 36 309715 = 10673712 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 309715) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 309715) (weight := fun _ => 1) (xs := [129, 161, 401, 405, 433, 437, 465, 469, 497, 501, 649, 651, 681, 683, 921, 923, 925, 927, 953, 955, 957, 959, 985, 987, 989, 991, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover309715 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h81866 : P.leaf 36 81866 = 10673712 :=
  orient74 (v := 309715) (by decide) (by decide +kernel) h309715

theorem cover302999 : P.CoversSplit 26 10 302999 0xff00040000330000000000000000000000000000000000000000000000000000ff00040000330000000000000000000000000000000000000000000000000000ff00040000330000000000000000000000000000000000000000000000000000ff00040000330000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 531, 538, 923, 930, 1265, 1272, 1273]) (by decide +kernel)

theorem c302999_0 : P.sumLeaves 26 310270976 1024 = 59134118 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 302999) (lo := 0) (len := 1024) (W := 59134118) check rows elimOK (by decide) (by decide) cover302999 (by decide)
  decide +kernel

theorem h302999 : P.leaf 36 302999 = 59134118 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 59134118)]) (.cons c302999_0 (.nil)) (by decide) (by decide))

theorem h81867 : P.leaf 36 81867 = 59134118 :=
  orient6 (v := 302999) (by decide) (by decide +kernel) h302999

theorem cover309723 : P.CoversSplit 26 10 309723 0xaaaa0000aaaa0000aaaa0000aaaa000000000000000000000000000000000000000000000000000000000a0a00000a0a0000000000000000000000000000000000220000002200000022000000220000000000000000000000000000000000000000000000000000000000020000000200000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 629, 636, 1273, 1308, 1665]) (by decide +kernel)

theorem c309723_0 : P.sumLeaves 26 317156352 1024 = 43703069 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 309723) (lo := 0) (len := 1024) (W := 43703069) check rows elimOK (by decide) (by decide) cover309723 (by decide)
  decide +kernel

theorem h309723 : P.leaf 36 309723 = 43703069 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 43703069)]) (.cons c309723_0 (.nil)) (by decide) (by decide))

theorem h81870 : P.leaf 36 81870 = 43703069 :=
  orient74 (v := 309723) (by decide) (by decide +kernel) h309723

theorem cover303007 : P.CoversSplit 26 10 303007 0xffff050500330001000000000000000000000000000000000000000000000000ffff050500330001000000000000000000000000000000000000000000000000ffff050500330001000000000000000000000000000000000000000000000000ffff050500330001000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 1265, 1266, 1272, 1273]) (by decide +kernel)

noncomputable def f303007 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (310279168 + i)

theorem c303007_0 : rowSum f303007 0 1024 = 235375149 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 303007) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover303007 (by decide)
  decide +kernel

theorem sum303007 : rowSum f303007 0 1024 = 235375149 :=
  c303007_0

theorem h303007 : P.leaf 36 303007 = 235375149 :=
  leaf_weighted (k := 26) (d := 10) (H := 303007) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 303007) (by decide) (by decide +kernel)) sum303007

theorem h81871 : P.leaf 36 81871 = 235375149 :=
  orient6 (v := 303007) (by decide) (by decide +kernel) h303007

theorem cover303030 : P.CoversSplit 26 10 303030 0xff00ff0000330032000000000000000000000000003300330000000000000000ff00ff0000330032000000000000000000000000003300330000000000000000ff00ff0000330032000000000000000000000000000000000000000000000000ff00ff0000330032000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [489, 538, 922, 923, 930, 1273]) (ps := [(15, [922], [930])]) (by decide +kernel)

noncomputable def f303030 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (310302720 + i)

theorem c303030_0 : rowSum f303030 0 1024 = 93851052 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 303030) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover303030 (by decide)
  decide +kernel

theorem sum303030 : rowSum f303030 0 1024 = 93851052 :=
  c303030_0

theorem h303030 : P.leaf 36 303030 = 93851052 :=
  leaf_weighted (k := 26) (d := 10) (H := 303030) (keep := keep3) (twice := twice3) rows (by decide) (by decide) (bal3) (invRow3 (H := 303030) (by decide) (by decide +kernel)) sum303030

theorem h81882 : P.leaf 36 81882 = 93851052 :=
  orient6 (v := 303030) (by decide) (by decide +kernel) h303030

theorem cover303031 : P.CoversSplit 26 10 303031 0xff00ff0000330032000000000000000000000000003300330000000000000000ff00ff0000330032000000000000000000000000003300330000000000000000ff00ff0000330032000000000000000000000000000000000000000000000000ff00ff0000330032000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [489, 922, 923, 930, 1273]) (ps := [(15, [922], [930])]) (by decide +kernel)

noncomputable def f303031 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (310303744 + i)

theorem c303031_0 : rowSum f303031 0 1024 = 170353998 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 303031) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover303031 (by decide)
  decide +kernel

theorem sum303031 : rowSum f303031 0 1024 = 170353998 :=
  c303031_0

theorem h303031 : P.leaf 36 303031 = 170353998 :=
  leaf_weighted (k := 26) (d := 10) (H := 303031) (keep := keep3) (twice := twice3) rows (by decide) (by decide) (bal3) (invRow3 (H := 303031) (by decide) (by decide +kernel)) sum303031

theorem h81883 : P.leaf 36 81883 = 170353998 :=
  orient6 (v := 303031) (by decide) (by decide +kernel) h303031

theorem cover303034 : P.CoversSplit 26 10 303034 0xf0f0f5f500300030000000000000000000000000000000000000000000000000f0f0f5f500300030000000000000000000000000000000000000000000000000f0f0f5f500300030000000000000000000000000000000000000000000000000f0f0f5f500300030000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [481, 538, 922, 929, 1265, 1266, 1273]) (ps := [(15, [930], [922])]) (by decide +kernel)

noncomputable def f303034 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (310306816 + i)

theorem c303034_0 : rowSum f303034 0 1024 = 133636886 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 303034) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover303034 (by decide)
  decide +kernel

theorem sum303034 : rowSum f303034 0 1024 = 133636886 :=
  c303034_0

theorem h303034 : P.leaf 36 303034 = 133636886 :=
  leaf_weighted (k := 26) (d := 10) (H := 303034) (keep := keep4) (twice := twice4) rows (by decide) (by decide) (bal4) (invRow4 (H := 303034) (by decide) (by decide +kernel)) sum303034

theorem h81884 : P.leaf 36 81884 = 133636886 :=
  orient6 (v := 303034) (by decide) (by decide +kernel) h303034

theorem cover303035 : P.CoversSplit 26 10 303035 0xf0f0f5f500300030000000000000000000000000000000000000000000000000f0f0f5f500300030000000000000000000000000000000000000000000000000f0f0f5f500300030000000000000000000000000000000000000000000000000f0f0f5f500300030000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [481, 538, 922, 929, 1265, 1266, 1273]) (ps := [(15, [930], [922])]) (by decide +kernel)

noncomputable def f303035 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (310307840 + i)

theorem c303035_0 : rowSum f303035 0 1024 = 252664580 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 303035) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover303035 (by decide)
  decide +kernel

theorem sum303035 : rowSum f303035 0 1024 = 252664580 :=
  c303035_0

theorem h303035 : P.leaf 36 303035 = 252664580 :=
  leaf_weighted (k := 26) (d := 10) (H := 303035) (keep := keep4) (twice := twice4) rows (by decide) (by decide) (bal4) (invRow4 (H := 303035) (by decide) (by decide +kernel)) sum303035

theorem h81885 : P.leaf 36 81885 = 252664580 :=
  orient6 (v := 303035) (by decide) (by decide +kernel) h303035

theorem cover303038 : P.CoversSplit 26 10 303038 0xffffffff00330032000000000000000000330033000000000000000000000000ffffffff00330032000000000000000000330033000000000000000000000000ffffffff00330032000000000000000000000000000000000000000000000000ffffffff00330032000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [538, 922, 930, 1266, 1273, 1665]) (ps := [(19, [1265], [1273])]) (by decide +kernel)

theorem c303038_0 : P.sumLeaves 26 310310912 739 = 157289635 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 303038) (lo := 0) (len := 739) (W := 157289635) check rows elimOK (by decide) (by decide) cover303038 (by decide)
  decide +kernel

theorem c303038_1 : P.sumLeaves 26 310311651 285 = 200271141 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 303038) (lo := 739) (len := 285) (W := 200271141) check rows elimOK (by decide) (by decide) cover303038 (by decide)
  decide +kernel

theorem h303038 : P.leaf 36 303038 = 357560776 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(739, 157289635), (285, 200271141)]) (.cons c303038_0 (.cons c303038_1 (.nil))) (by decide) (by decide))

theorem h81886 : P.leaf 36 81886 = 357560776 :=
  orient6 (v := 303038) (by decide) (by decide +kernel) h303038

theorem cover303039 : P.CoversSplit 26 10 303039 0xffffffff00330032000000000000000000330033000000000000000000000000ffffffff00330032000000000000000000330033000000000000000000000000ffffffff00330032000000000000000000000000000000000000000000000000ffffffff00330032000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [538, 922, 930, 1266, 1273, 1665]) (ps := [(19, [1265], [1273])]) (by decide +kernel)

theorem c303039_0 : P.sumLeaves 26 310311936 739 = 275034783 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 303039) (lo := 0) (len := 739) (W := 275034783) check rows elimOK (by decide) (by decide) cover303039 (by decide)
  decide +kernel

theorem c303039_1 : P.sumLeaves 26 310312675 285 = 334816738 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 303039) (lo := 739) (len := 285) (W := 334816738) check rows elimOK (by decide) (by decide) cover303039 (by decide)
  decide +kernel

theorem h303039 : P.leaf 36 303039 = 609851521 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(739, 275034783), (285, 334816738)]) (.cons c303039_0 (.cons c303039_1 (.nil))) (by decide) (by decide))

theorem h81887 : P.leaf 36 81887 = 609851521 :=
  orient6 (v := 303039) (by decide) (by decide +kernel) h303039

theorem cover81918 : P.CoversSplit 26 10 81918 0xfffffffafffffafafffffffafffffafafffffffafffcfac8aaaaaaaaaa88aa88fffffafafffffafaaaaaaaaaaaaaaaaafffffafafffcfac8aaaaaaaaaa88aa88fffffffafffffafafffffffafffffafafffffffaffccfac8aaaaaaaaaa88aa880000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [874, 930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f81918 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (83884032 + i)

theorem c81918_0 : rowSum f81918 0 468 = 313919746 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 81918) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover81918 (by decide)
  decide +kernel

theorem c81918_1 : rowSum f81918 468 242 = 410948238 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 81918) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover81918 (by decide)
  decide +kernel

theorem c81918_2 : rowSum f81918 710 210 = 561149830 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 81918) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover81918 (by decide)
  decide +kernel

theorem c81918_3 : rowSum f81918 920 104 = 669619438 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 81918) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover81918 (by decide)
  decide +kernel

theorem sum81918 : rowSum f81918 0 1024 = 1955637252 :=
  rowSum_append (F := f81918) (lo := 0) (n := 468) (m := 556) (A := 313919746) (B := 1641717506) c81918_0 (rowSum_append (F := f81918) (lo := 468) (n := 242) (m := 314) (A := 410948238) (B := 1230769268) c81918_1 (rowSum_append (F := f81918) (lo := 710) (n := 210) (m := 104) (A := 561149830) (B := 669619438) c81918_2 (c81918_3)))

theorem h81918 : P.leaf 36 81918 = 1955637252 :=
  leaf_weighted (k := 26) (d := 10) (H := 81918) (keep := keep3) (twice := twice3) rows (by decide) (by decide) (bal3) (invRow3 (H := 81918) (by decide) (by decide +kernel)) sum81918

theorem cover303103 : P.CoversSplit 26 10 303103 0xfffffffffffffffffffffafafffffafaffffffffffccffcc8888888888888888ffffffffffffffffaaaaaaaaaaaaaaaaffffffffffccffcc8888888888888888fffffffffffffffffffffafafffffafacccccccccccccccc8888888888888888ffffffffffffffffaaaaaaaaaaaaaaaacccccccccccccccc8888888888888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [922, 930, 1658, 1665]) (by decide +kernel)

noncomputable def f303103 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (310377472 + i)

theorem c303103_0 : rowSum f303103 0 326 = 721614118 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 303103) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover303103 (by decide)
  decide +kernel

theorem c303103_1 : rowSum f303103 326 132 = 780338374 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 303103) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover303103 (by decide)
  decide +kernel

theorem c303103_2 : rowSum f303103 458 414 = 1132263980 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 303103) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover303103 (by decide)
  decide +kernel

theorem c303103_3 : rowSum f303103 872 152 = 797313551 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 303103) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover303103 (by decide)
  decide +kernel

theorem sum303103 : rowSum f303103 0 1024 = 3431530023 :=
  rowSum_append (F := f303103) (lo := 0) (n := 326) (m := 698) (A := 721614118) (B := 2709915905) c303103_0 (rowSum_append (F := f303103) (lo := 326) (n := 132) (m := 566) (A := 780338374) (B := 1929577531) c303103_1 (rowSum_append (F := f303103) (lo := 458) (n := 414) (m := 152) (A := 1132263980) (B := 797313551) c303103_2 (c303103_3)))

theorem h303103 : P.leaf 36 303103 = 3431530023 :=
  leaf_weighted (k := 26) (d := 10) (H := 303103) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 303103) (by decide) (by decide +kernel)) sum303103

theorem h81919 : P.leaf 36 81919 = 3431530023 :=
  orient6 (v := 303103) (by decide) (by decide +kernel) h303103

def seg : List (ℕ × ℕ) := [(81865, 180), (81866, 720), (81867, 720), (81870, 360), (81871, 360), (81882, 360), (81883, 360), (81884, 360), (81885, 360), (81886, 720), (81887, 720), (81918, 180), (81919, 180)]

theorem segOK : checkSeg 20 perms 81865 88517 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 81865 88517 5580 2053365435900 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 2053365435900)
    (SegSum.cons (w := 180) h81865 (SegSum.cons (w := 720) h81866 (SegSum.cons (w := 720) h81867 (SegSum.cons (w := 360) h81870 (SegSum.cons (w := 360) h81871 (SegSum.cons (w := 360) h81882 (SegSum.cons (w := 360) h81883 (SegSum.cons (w := 360) h81884 (SegSum.cons (w := 360) h81885 (SegSum.cons (w := 720) h81886 (SegSum.cons (w := 720) h81887 (SegSum.cons (w := 180) h81918 (SegSum.cons (w := 180) h81919 (show SegSum (P.leaf 36) [] 0 from rfl)))))))))))))) (by decide)

end RACert.S6N0.C0.S52
