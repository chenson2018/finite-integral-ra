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

namespace RACert.S6N0.C0.S11

open RACert RACert.Problem

theorem cover3930 : P.CoversSplit 26 10 3930 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3930 : P.leaf 36 3930 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3930) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3930) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3930 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3931 : P.CoversSplit 26 10 3931 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3931 : P.leaf 36 3931 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3931) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3931) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3931 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3932 : P.CoversSplit 26 10 3932 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem h3932 : P.leaf 36 3932 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3932) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3932) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3932 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3933 : P.CoversSplit 26 10 3933 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem h3933 : P.leaf 36 3933 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3933) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3933) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3933 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3934 : P.CoversSplit 26 10 3934 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3934 : P.leaf 36 3934 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3934) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3934) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3934 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3935 : P.CoversSplit 26 10 3935 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3935 : P.leaf 36 3935 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3935) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3935) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3935 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3966 : P.CoversSplit 26 10 3966 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3966 : P.leaf 36 3966 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3966) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3966) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3966 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3967 : P.CoversSplit 26 10 3967 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3967 : P.leaf 36 3967 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3967) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3967) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3967 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3968 : P.CoversSplit 26 10 3968 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [468]) (by decide +kernel)

theorem h3968 : P.leaf 36 3968 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3968) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3968) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3968 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3969 : P.CoversSplit 26 10 3969 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [481, 489, 530, 538, 608, 881, 922, 930, 979, 1658, 1665]) (ps := [(13, [510], [972])]) (by decide +kernel)

theorem h3969 : P.leaf 36 3969 = 64 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3969) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3969) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover3969 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3970 : P.CoversSplit 26 10 3970 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [468]) (by decide +kernel)

theorem h3970 : P.leaf 36 3970 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3970) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3970) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3970 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3971 : P.CoversSplit 26 10 3971 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3971 : P.leaf 36 3971 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3971) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3971) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3971 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3974 : P.CoversSplit 26 10 3974 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [468]) (by decide +kernel)

theorem h3974 : P.leaf 36 3974 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3974) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3974) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3974 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3975 : P.CoversSplit 26 10 3975 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3975 : P.leaf 36 3975 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3975) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3975) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3975 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3976 : P.CoversSplit 26 10 3976 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3976 : P.leaf 36 3976 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3976) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3976) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3976 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3977 : P.CoversSplit 26 10 3977 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3977 : P.leaf 36 3977 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3977) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3977) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3977 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3978 : P.CoversSplit 26 10 3978 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem h3978 : P.leaf 36 3978 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3978) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3978) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3978 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3979 : P.CoversSplit 26 10 3979 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem h3979 : P.leaf 36 3979 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3979) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3979) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3979 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover10587 : P.CoversSplit 26 10 10587 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 482, 530, 579, 629, 636, 972, 979, 1265, 1322, 1665]) (by decide +kernel)

theorem h10587 : P.leaf 36 10587 = 7168 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 10587) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 10587) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover10587 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h3982 : P.leaf 36 3982 = 7168 :=
  orient72 (v := 10587) (by decide) (by decide +kernel) h10587

theorem cover10591 : P.CoversSplit 26 10 10591 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 880, 972, 979, 1265, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h10591 : P.leaf 36 10591 = 101528 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 10591) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 10591) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover10591 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h3983 : P.leaf 36 3983 = 101528 :=
  orient72 (v := 10591) (by decide) (by decide +kernel) h10591

theorem cover3986 : P.CoversSplit 26 10 3986 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [468]) (by decide +kernel)

theorem h3986 : P.leaf 36 3986 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3986) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3986) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3986 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3987 : P.CoversSplit 26 10 3987 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3987 : P.leaf 36 3987 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3987) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3987) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3987 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3988 : P.CoversSplit 26 10 3988 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [468]) (by decide +kernel)

theorem h3988 : P.leaf 36 3988 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3988) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3988) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3988 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3989 : P.CoversSplit 26 10 3989 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem h3989 : P.leaf 36 3989 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3989) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3989) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3989 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3990 : P.CoversSplit 26 10 3990 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [468]) (by decide +kernel)

theorem h3990 : P.leaf 36 3990 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3990) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3990) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3990 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3991 : P.CoversSplit 26 10 3991 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3991 : P.leaf 36 3991 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3991) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3991) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3991 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3992 : P.CoversSplit 26 10 3992 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3992 : P.leaf 36 3992 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3992) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3992) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3992 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3993 : P.CoversSplit 26 10 3993 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3993 : P.leaf 36 3993 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3993) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3993) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3993 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3994 : P.CoversSplit 26 10 3994 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem h3994 : P.leaf 36 3994 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3994) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3994) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3994 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3995 : P.CoversSplit 26 10 3995 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem h3995 : P.leaf 36 3995 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3995) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3995) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3995 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3996 : P.CoversSplit 26 10 3996 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3996 : P.leaf 36 3996 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3996) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3996) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3996 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3997 : P.CoversSplit 26 10 3997 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3997 : P.leaf 36 3997 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3997) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3997) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3997 (by decide) (by decide) (by decide +kernel)
  decide +kernel

def seg : List (ℕ × ℕ) := [(3930, 360), (3931, 360), (3932, 360), (3933, 360), (3934, 720), (3935, 720), (3966, 180), (3967, 180), (3968, 180), (3969, 180), (3970, 720), (3971, 720), (3974, 360), (3975, 360), (3976, 360), (3977, 360), (3978, 720), (3979, 720), (3982, 360), (3983, 360), (3986, 360), (3987, 360), (3988, 360), (3989, 360), (3990, 720), (3991, 720), (3992, 720), (3993, 720), (3994, 720), (3995, 720), (3996, 720), (3997, 720)]

theorem segOK : checkSeg 20 perms 3930 3998 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 3930 3998 15840 39142080 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 39142080)
    (SegSum.cons (w := 360) h3930 (SegSum.cons (w := 360) h3931 (SegSum.cons (w := 360) h3932 (SegSum.cons (w := 360) h3933 (SegSum.cons (w := 720) h3934 (SegSum.cons (w := 720) h3935 (SegSum.cons (w := 180) h3966 (SegSum.cons (w := 180) h3967 (SegSum.cons (w := 180) h3968 (SegSum.cons (w := 180) h3969 (SegSum.cons (w := 720) h3970 (SegSum.cons (w := 720) h3971 (SegSum.cons (w := 360) h3974 (SegSum.cons (w := 360) h3975 (SegSum.cons (w := 360) h3976 (SegSum.cons (w := 360) h3977 (SegSum.cons (w := 720) h3978 (SegSum.cons (w := 720) h3979 (SegSum.cons (w := 360) h3982 (SegSum.cons (w := 360) h3983 (SegSum.cons (w := 360) h3986 (SegSum.cons (w := 360) h3987 (SegSum.cons (w := 360) h3988 (SegSum.cons (w := 360) h3989 (SegSum.cons (w := 720) h3990 (SegSum.cons (w := 720) h3991 (SegSum.cons (w := 720) h3992 (SegSum.cons (w := 720) h3993 (SegSum.cons (w := 720) h3994 (SegSum.cons (w := 720) h3995 (SegSum.cons (w := 720) h3996 (SegSum.cons (w := 720) h3997 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S11
