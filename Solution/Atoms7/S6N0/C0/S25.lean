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

theorem c13911_0 : P.sumLeaves 26 14244864 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13911) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13911 (by decide)
  decide +kernel

theorem h13911 : P.leaf 36 13911 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13911_0 (.nil)) (by decide) (by decide))

theorem cover13914 : P.CoversSplit 26 10 13914 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [467]) (by decide +kernel)

theorem c13914_0 : P.sumLeaves 26 14247936 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13914) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13914 (by decide)
  decide +kernel

theorem h13914 : P.leaf 36 13914 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13914_0 (.nil)) (by decide) (by decide))

theorem cover13915 : P.CoversSplit 26 10 13915 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c13915_0 : P.sumLeaves 26 14248960 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13915) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13915 (by decide)
  decide +kernel

theorem h13915 : P.leaf 36 13915 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13915_0 (.nil)) (by decide) (by decide))

theorem cover13918 : P.CoversSplit 26 10 13918 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c13918_0 : P.sumLeaves 26 14252032 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13918) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13918 (by decide)
  decide +kernel

theorem h13918 : P.leaf 36 13918 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13918_0 (.nil)) (by decide) (by decide))

theorem cover13919 : P.CoversSplit 26 10 13919 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c13919_0 : P.sumLeaves 26 14253056 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13919) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13919 (by decide)
  decide +kernel

theorem h13919 : P.leaf 36 13919 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13919_0 (.nil)) (by decide) (by decide))

theorem cover13938 : P.CoversSplit 26 10 13938 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c13938_0 : P.sumLeaves 26 14272512 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13938) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13938 (by decide)
  decide +kernel

theorem h13938 : P.leaf 36 13938 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13938_0 (.nil)) (by decide) (by decide))

theorem cover13939 : P.CoversSplit 26 10 13939 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c13939_0 : P.sumLeaves 26 14273536 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13939) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13939 (by decide)
  decide +kernel

theorem h13939 : P.leaf 36 13939 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13939_0 (.nil)) (by decide) (by decide))

theorem cover13942 : P.CoversSplit 26 10 13942 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c13942_0 : P.sumLeaves 26 14276608 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13942) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13942 (by decide)
  decide +kernel

theorem h13942 : P.leaf 36 13942 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13942_0 (.nil)) (by decide) (by decide))

theorem cover13943 : P.CoversSplit 26 10 13943 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c13943_0 : P.sumLeaves 26 14277632 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13943) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13943 (by decide)
  decide +kernel

theorem h13943 : P.leaf 36 13943 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13943_0 (.nil)) (by decide) (by decide))

theorem cover13944 : P.CoversSplit 26 10 13944 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c13944_0 : P.sumLeaves 26 14278656 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13944) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13944 (by decide)
  decide +kernel

theorem h13944 : P.leaf 36 13944 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13944_0 (.nil)) (by decide) (by decide))

theorem cover13945 : P.CoversSplit 26 10 13945 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c13945_0 : P.sumLeaves 26 14279680 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13945) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13945 (by decide)
  decide +kernel

theorem h13945 : P.leaf 36 13945 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13945_0 (.nil)) (by decide) (by decide))

theorem cover13946 : P.CoversSplit 26 10 13946 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c13946_0 : P.sumLeaves 26 14280704 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13946) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13946 (by decide)
  decide +kernel

theorem h13946 : P.leaf 36 13946 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13946_0 (.nil)) (by decide) (by decide))

theorem cover13947 : P.CoversSplit 26 10 13947 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c13947_0 : P.sumLeaves 26 14281728 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13947) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13947 (by decide)
  decide +kernel

theorem h13947 : P.leaf 36 13947 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13947_0 (.nil)) (by decide) (by decide))

theorem cover13948 : P.CoversSplit 26 10 13948 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c13948_0 : P.sumLeaves 26 14282752 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13948) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13948 (by decide)
  decide +kernel

theorem h13948 : P.leaf 36 13948 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13948_0 (.nil)) (by decide) (by decide))

theorem cover13949 : P.CoversSplit 26 10 13949 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c13949_0 : P.sumLeaves 26 14283776 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13949) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13949 (by decide)
  decide +kernel

theorem h13949 : P.leaf 36 13949 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13949_0 (.nil)) (by decide) (by decide))

theorem cover13950 : P.CoversSplit 26 10 13950 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c13950_0 : P.sumLeaves 26 14284800 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13950) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13950 (by decide)
  decide +kernel

theorem h13950 : P.leaf 36 13950 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13950_0 (.nil)) (by decide) (by decide))

theorem cover13951 : P.CoversSplit 26 10 13951 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c13951_0 : P.sumLeaves 26 14285824 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13951) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13951 (by decide)
  decide +kernel

theorem h13951 : P.leaf 36 13951 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13951_0 (.nil)) (by decide) (by decide))

theorem cover14001 : P.CoversSplit 26 10 14001 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [475]) (by decide +kernel)

theorem c14001_0 : P.sumLeaves 26 14337024 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14001) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14001 (by decide)
  decide +kernel

theorem h14001 : P.leaf 36 14001 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14001_0 (.nil)) (by decide) (by decide))

theorem cover14002 : P.CoversSplit 26 10 14002 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c14002_0 : P.sumLeaves 26 14338048 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14002) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14002 (by decide)
  decide +kernel

theorem h14002 : P.leaf 36 14002 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14002_0 (.nil)) (by decide) (by decide))

theorem cover14003 : P.CoversSplit 26 10 14003 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c14003_0 : P.sumLeaves 26 14339072 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14003) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14003 (by decide)
  decide +kernel

theorem h14003 : P.leaf 36 14003 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14003_0 (.nil)) (by decide) (by decide))

theorem cover14004 : P.CoversSplit 26 10 14004 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [475]) (by decide +kernel)

theorem c14004_0 : P.sumLeaves 26 14340096 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14004) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14004 (by decide)
  decide +kernel

theorem h14004 : P.leaf 36 14004 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14004_0 (.nil)) (by decide) (by decide))

theorem cover14005 : P.CoversSplit 26 10 14005 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [475]) (by decide +kernel)

theorem c14005_0 : P.sumLeaves 26 14341120 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14005) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14005 (by decide)
  decide +kernel

theorem h14005 : P.leaf 36 14005 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14005_0 (.nil)) (by decide) (by decide))

theorem cover14006 : P.CoversSplit 26 10 14006 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c14006_0 : P.sumLeaves 26 14342144 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14006) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14006 (by decide)
  decide +kernel

theorem h14006 : P.leaf 36 14006 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14006_0 (.nil)) (by decide) (by decide))

theorem cover14007 : P.CoversSplit 26 10 14007 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c14007_0 : P.sumLeaves 26 14343168 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14007) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14007 (by decide)
  decide +kernel

theorem h14007 : P.leaf 36 14007 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14007_0 (.nil)) (by decide) (by decide))

theorem cover14008 : P.CoversSplit 26 10 14008 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c14008_0 : P.sumLeaves 26 14344192 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14008) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14008 (by decide)
  decide +kernel

theorem h14008 : P.leaf 36 14008 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14008_0 (.nil)) (by decide) (by decide))

theorem cover14009 : P.CoversSplit 26 10 14009 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c14009_0 : P.sumLeaves 26 14345216 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14009) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14009 (by decide)
  decide +kernel

theorem h14009 : P.leaf 36 14009 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14009_0 (.nil)) (by decide) (by decide))

theorem cover14010 : P.CoversSplit 26 10 14010 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c14010_0 : P.sumLeaves 26 14346240 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14010) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14010 (by decide)
  decide +kernel

theorem h14010 : P.leaf 36 14010 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14010_0 (.nil)) (by decide) (by decide))

theorem cover14011 : P.CoversSplit 26 10 14011 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c14011_0 : P.sumLeaves 26 14347264 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14011) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14011 (by decide)
  decide +kernel

theorem h14011 : P.leaf 36 14011 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14011_0 (.nil)) (by decide) (by decide))

theorem cover14012 : P.CoversSplit 26 10 14012 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c14012_0 : P.sumLeaves 26 14348288 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14012) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14012 (by decide)
  decide +kernel

theorem h14012 : P.leaf 36 14012 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14012_0 (.nil)) (by decide) (by decide))

theorem cover14013 : P.CoversSplit 26 10 14013 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c14013_0 : P.sumLeaves 26 14349312 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14013) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14013 (by decide)
  decide +kernel

theorem h14013 : P.leaf 36 14013 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14013_0 (.nil)) (by decide) (by decide))

theorem cover14014 : P.CoversSplit 26 10 14014 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c14014_0 : P.sumLeaves 26 14350336 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14014) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14014 (by decide)
  decide +kernel

theorem h14014 : P.leaf 36 14014 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14014_0 (.nil)) (by decide) (by decide))

theorem cover14015 : P.CoversSplit 26 10 14015 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c14015_0 : P.sumLeaves 26 14351360 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14015) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14015 (by decide)
  decide +kernel

theorem h14015 : P.leaf 36 14015 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14015_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(13911, 720), (13914, 360), (13915, 360), (13918, 360), (13919, 360), (13938, 720), (13939, 720), (13942, 720), (13943, 720), (13944, 720), (13945, 720), (13946, 720), (13947, 720), (13948, 720), (13949, 720), (13950, 720), (13951, 720), (14001, 360), (14002, 720), (14003, 720), (14004, 360), (14005, 720), (14006, 720), (14007, 720), (14008, 720), (14009, 720), (14010, 720), (14011, 720), (14012, 720), (14013, 720), (14014, 720), (14015, 720)]

theorem segOK : checkSeg 20 perms 13911 14016 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 13911 14016 20880 0 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 0)
    (SegSum.cons (w := 720) h13911 (SegSum.cons (w := 360) h13914 (SegSum.cons (w := 360) h13915 (SegSum.cons (w := 360) h13918 (SegSum.cons (w := 360) h13919 (SegSum.cons (w := 720) h13938 (SegSum.cons (w := 720) h13939 (SegSum.cons (w := 720) h13942 (SegSum.cons (w := 720) h13943 (SegSum.cons (w := 720) h13944 (SegSum.cons (w := 720) h13945 (SegSum.cons (w := 720) h13946 (SegSum.cons (w := 720) h13947 (SegSum.cons (w := 720) h13948 (SegSum.cons (w := 720) h13949 (SegSum.cons (w := 720) h13950 (SegSum.cons (w := 720) h13951 (SegSum.cons (w := 360) h14001 (SegSum.cons (w := 720) h14002 (SegSum.cons (w := 720) h14003 (SegSum.cons (w := 360) h14004 (SegSum.cons (w := 720) h14005 (SegSum.cons (w := 720) h14006 (SegSum.cons (w := 720) h14007 (SegSum.cons (w := 720) h14008 (SegSum.cons (w := 720) h14009 (SegSum.cons (w := 720) h14010 (SegSum.cons (w := 720) h14011 (SegSum.cons (w := 720) h14012 (SegSum.cons (w := 720) h14013 (SegSum.cons (w := 720) h14014 (SegSum.cons (w := 720) h14015 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S25
