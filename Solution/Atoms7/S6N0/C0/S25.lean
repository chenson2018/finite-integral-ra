/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S6N0.C0.Defs

/-! Generated certificate for the identity on six symmetric diversity atoms. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S6N0.C0.S25

open RACert RACert.Problem

theorem cover13804 : P.CoversSplit 26 10 13804 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13804_0 : P.sumLeaves 26 14135296 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13804) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13804 (by decide)
  decide +kernel

theorem h13804 : P.leaf 36 13804 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13804_0 (.nil)) (by decide) (by decide))

theorem cover13805 : P.CoversSplit 26 10 13805 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13805_0 : P.sumLeaves 26 14136320 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13805) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13805 (by decide)
  decide +kernel

theorem h13805 : P.leaf 36 13805 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13805_0 (.nil)) (by decide) (by decide))

theorem cover13807 : P.CoversSplit 26 10 13807 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13807_0 : P.sumLeaves 26 14138368 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13807) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13807 (by decide)
  decide +kernel

theorem h13807 : P.leaf 36 13807 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13807_0 (.nil)) (by decide) (by decide))

theorem cover13808 : P.CoversSplit 26 10 13808 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c13808_0 : P.sumLeaves 26 14139392 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13808) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13808 (by decide)
  decide +kernel

theorem h13808 : P.leaf 36 13808 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13808_0 (.nil)) (by decide) (by decide))

theorem cover13809 : P.CoversSplit 26 10 13809 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c13809_0 : P.sumLeaves 26 14140416 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13809) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13809 (by decide)
  decide +kernel

theorem h13809 : P.leaf 36 13809 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13809_0 (.nil)) (by decide) (by decide))

theorem cover13811 : P.CoversSplit 26 10 13811 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c13811_0 : P.sumLeaves 26 14142464 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13811) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13811 (by decide)
  decide +kernel

theorem h13811 : P.leaf 36 13811 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13811_0 (.nil)) (by decide) (by decide))

theorem cover13812 : P.CoversSplit 26 10 13812 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13812_0 : P.sumLeaves 26 14143488 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13812) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13812 (by decide)
  decide +kernel

theorem h13812 : P.leaf 36 13812 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13812_0 (.nil)) (by decide) (by decide))

theorem cover13813 : P.CoversSplit 26 10 13813 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13813_0 : P.sumLeaves 26 14144512 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13813) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13813 (by decide)
  decide +kernel

theorem h13813 : P.leaf 36 13813 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13813_0 (.nil)) (by decide) (by decide))

theorem cover13814 : P.CoversSplit 26 10 13814 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13814_0 : P.sumLeaves 26 14145536 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13814) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13814 (by decide)
  decide +kernel

theorem h13814 : P.leaf 36 13814 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13814_0 (.nil)) (by decide) (by decide))

theorem cover13815 : P.CoversSplit 26 10 13815 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13815_0 : P.sumLeaves 26 14146560 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13815) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13815 (by decide)
  decide +kernel

theorem h13815 : P.leaf 36 13815 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13815_0 (.nil)) (by decide) (by decide))

theorem cover13820 : P.CoversSplit 26 10 13820 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13820_0 : P.sumLeaves 26 14151680 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13820) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13820 (by decide)
  decide +kernel

theorem h13820 : P.leaf 36 13820 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13820_0 (.nil)) (by decide) (by decide))

theorem cover13821 : P.CoversSplit 26 10 13821 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13821_0 : P.sumLeaves 26 14152704 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13821) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13821 (by decide)
  decide +kernel

theorem h13821 : P.leaf 36 13821 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13821_0 (.nil)) (by decide) (by decide))

theorem cover13823 : P.CoversSplit 26 10 13823 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13823_0 : P.sumLeaves 26 14154752 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13823) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13823 (by decide)
  decide +kernel

theorem h13823 : P.leaf 36 13823 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13823_0 (.nil)) (by decide) (by decide))

theorem cover13906 : P.CoversSplit 26 10 13906 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [467]) (by decide +kernel)

theorem c13906_0 : P.sumLeaves 26 14239744 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13906) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13906 (by decide)
  decide +kernel

theorem h13906 : P.leaf 36 13906 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13906_0 (.nil)) (by decide) (by decide))

theorem cover13907 : P.CoversSplit 26 10 13907 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c13907_0 : P.sumLeaves 26 14240768 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13907) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13907 (by decide)
  decide +kernel

theorem h13907 : P.leaf 36 13907 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13907_0 (.nil)) (by decide) (by decide))

theorem cover13910 : P.CoversSplit 26 10 13910 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c13910_0 : P.sumLeaves 26 14243840 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13910) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13910 (by decide)
  decide +kernel

theorem h13910 : P.leaf 36 13910 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13910_0 (.nil)) (by decide) (by decide))

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

def seg : List (ℕ × ℕ) := [(13804, 360), (13805, 720), (13807, 360), (13808, 360), (13809, 720), (13811, 360), (13812, 720), (13813, 720), (13814, 720), (13815, 720), (13820, 360), (13821, 720), (13823, 360), (13906, 720), (13907, 720), (13910, 720), (13911, 720), (13914, 360), (13915, 360), (13918, 360), (13919, 360), (13938, 720), (13939, 720), (13942, 720), (13943, 720), (13944, 720), (13945, 720), (13946, 720), (13947, 720), (13948, 720), (13949, 720), (13950, 720)]

theorem segOK : checkSeg 20 perms 13804 13951 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 13804 13951 19440 0 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 0)
    (SegSum.cons (w := 360) h13804 (SegSum.cons (w := 720) h13805 (SegSum.cons (w := 360) h13807 (SegSum.cons (w := 360) h13808 (SegSum.cons (w := 720) h13809 (SegSum.cons (w := 360) h13811 (SegSum.cons (w := 720) h13812 (SegSum.cons (w := 720) h13813 (SegSum.cons (w := 720) h13814 (SegSum.cons (w := 720) h13815 (SegSum.cons (w := 360) h13820 (SegSum.cons (w := 720) h13821 (SegSum.cons (w := 360) h13823 (SegSum.cons (w := 720) h13906 (SegSum.cons (w := 720) h13907 (SegSum.cons (w := 720) h13910 (SegSum.cons (w := 720) h13911 (SegSum.cons (w := 360) h13914 (SegSum.cons (w := 360) h13915 (SegSum.cons (w := 360) h13918 (SegSum.cons (w := 360) h13919 (SegSum.cons (w := 720) h13938 (SegSum.cons (w := 720) h13939 (SegSum.cons (w := 720) h13942 (SegSum.cons (w := 720) h13943 (SegSum.cons (w := 720) h13944 (SegSum.cons (w := 720) h13945 (SegSum.cons (w := 720) h13946 (SegSum.cons (w := 720) h13947 (SegSum.cons (w := 720) h13948 (SegSum.cons (w := 720) h13949 (SegSum.cons (w := 720) h13950 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S25
