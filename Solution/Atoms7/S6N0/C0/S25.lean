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

namespace RACert.S6N0.C0.S25

open RACert RACert.Problem

theorem cover13911 : P.CoversSplit 26 10 13911 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h13911 : P.leaf 36 13911 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 13911) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 13911) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover13911 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover13914 : P.CoversSplit 26 10 13914 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [467]) (by decide +kernel)

theorem h13914 : P.leaf 36 13914 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 13914) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 13914) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover13914 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover13915 : P.CoversSplit 26 10 13915 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h13915 : P.leaf 36 13915 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 13915) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 13915) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover13915 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover13918 : P.CoversSplit 26 10 13918 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h13918 : P.leaf 36 13918 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 13918) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 13918) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover13918 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover13919 : P.CoversSplit 26 10 13919 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h13919 : P.leaf 36 13919 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 13919) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 13919) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover13919 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover13938 : P.CoversSplit 26 10 13938 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h13938 : P.leaf 36 13938 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 13938) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 13938) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover13938 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover13939 : P.CoversSplit 26 10 13939 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h13939 : P.leaf 36 13939 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 13939) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 13939) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover13939 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover13942 : P.CoversSplit 26 10 13942 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h13942 : P.leaf 36 13942 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 13942) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 13942) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover13942 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover13943 : P.CoversSplit 26 10 13943 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h13943 : P.leaf 36 13943 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 13943) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 13943) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover13943 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover13944 : P.CoversSplit 26 10 13944 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h13944 : P.leaf 36 13944 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 13944) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 13944) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover13944 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover13945 : P.CoversSplit 26 10 13945 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h13945 : P.leaf 36 13945 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 13945) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 13945) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover13945 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover13946 : P.CoversSplit 26 10 13946 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h13946 : P.leaf 36 13946 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 13946) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 13946) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover13946 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover13947 : P.CoversSplit 26 10 13947 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h13947 : P.leaf 36 13947 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 13947) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 13947) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover13947 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover13948 : P.CoversSplit 26 10 13948 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h13948 : P.leaf 36 13948 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 13948) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 13948) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover13948 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover13949 : P.CoversSplit 26 10 13949 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h13949 : P.leaf 36 13949 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 13949) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 13949) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover13949 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover13950 : P.CoversSplit 26 10 13950 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h13950 : P.leaf 36 13950 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 13950) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 13950) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover13950 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover13951 : P.CoversSplit 26 10 13951 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h13951 : P.leaf 36 13951 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 13951) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 13951) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover13951 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14001 : P.CoversSplit 26 10 14001 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [475]) (by decide +kernel)

theorem h14001 : P.leaf 36 14001 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14001) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14001) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14001 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14002 : P.CoversSplit 26 10 14002 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h14002 : P.leaf 36 14002 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14002) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14002) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14002 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14003 : P.CoversSplit 26 10 14003 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h14003 : P.leaf 36 14003 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14003) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14003) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14003 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14004 : P.CoversSplit 26 10 14004 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [475]) (by decide +kernel)

theorem h14004 : P.leaf 36 14004 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14004) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14004) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14004 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14005 : P.CoversSplit 26 10 14005 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [475]) (by decide +kernel)

theorem h14005 : P.leaf 36 14005 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14005) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14005) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14005 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14006 : P.CoversSplit 26 10 14006 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h14006 : P.leaf 36 14006 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14006) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14006) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14006 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14007 : P.CoversSplit 26 10 14007 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h14007 : P.leaf 36 14007 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14007) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14007) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14007 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14008 : P.CoversSplit 26 10 14008 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h14008 : P.leaf 36 14008 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14008) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14008) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14008 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14009 : P.CoversSplit 26 10 14009 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h14009 : P.leaf 36 14009 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14009) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14009) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14009 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14010 : P.CoversSplit 26 10 14010 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h14010 : P.leaf 36 14010 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14010) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14010) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14010 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14011 : P.CoversSplit 26 10 14011 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h14011 : P.leaf 36 14011 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14011) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14011) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14011 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14012 : P.CoversSplit 26 10 14012 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h14012 : P.leaf 36 14012 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14012) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14012) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14012 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14013 : P.CoversSplit 26 10 14013 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h14013 : P.leaf 36 14013 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14013) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14013) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14013 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14014 : P.CoversSplit 26 10 14014 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h14014 : P.leaf 36 14014 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14014) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14014) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14014 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14015 : P.CoversSplit 26 10 14015 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h14015 : P.leaf 36 14015 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14015) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14015) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14015 (by decide) (by decide) (by decide +kernel)
  decide +kernel

def seg : List (ℕ × ℕ) := [(13911, 720), (13914, 360), (13915, 360), (13918, 360), (13919, 360), (13938, 720), (13939, 720), (13942, 720), (13943, 720), (13944, 720), (13945, 720), (13946, 720), (13947, 720), (13948, 720), (13949, 720), (13950, 720), (13951, 720), (14001, 360), (14002, 720), (14003, 720), (14004, 360), (14005, 720), (14006, 720), (14007, 720), (14008, 720), (14009, 720), (14010, 720), (14011, 720), (14012, 720), (14013, 720), (14014, 720), (14015, 720)]

theorem segOK : checkSeg 20 perms 13911 14016 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 13911 14016 20880 0 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 0)
    (SegSum.cons (w := 720) h13911 (SegSum.cons (w := 360) h13914 (SegSum.cons (w := 360) h13915 (SegSum.cons (w := 360) h13918 (SegSum.cons (w := 360) h13919 (SegSum.cons (w := 720) h13938 (SegSum.cons (w := 720) h13939 (SegSum.cons (w := 720) h13942 (SegSum.cons (w := 720) h13943 (SegSum.cons (w := 720) h13944 (SegSum.cons (w := 720) h13945 (SegSum.cons (w := 720) h13946 (SegSum.cons (w := 720) h13947 (SegSum.cons (w := 720) h13948 (SegSum.cons (w := 720) h13949 (SegSum.cons (w := 720) h13950 (SegSum.cons (w := 720) h13951 (SegSum.cons (w := 360) h14001 (SegSum.cons (w := 720) h14002 (SegSum.cons (w := 720) h14003 (SegSum.cons (w := 360) h14004 (SegSum.cons (w := 720) h14005 (SegSum.cons (w := 720) h14006 (SegSum.cons (w := 720) h14007 (SegSum.cons (w := 720) h14008 (SegSum.cons (w := 720) h14009 (SegSum.cons (w := 720) h14010 (SegSum.cons (w := 720) h14011 (SegSum.cons (w := 720) h14012 (SegSum.cons (w := 720) h14013 (SegSum.cons (w := 720) h14014 (SegSum.cons (w := 720) h14015 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S25
