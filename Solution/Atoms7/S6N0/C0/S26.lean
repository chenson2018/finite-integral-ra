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

namespace RACert.S6N0.C0.S26

open RACert RACert.Problem

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

theorem cover14016 : P.CoversSplit 26 10 14016 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [467]) (by decide +kernel)

theorem c14016_0 : P.sumLeaves 26 14352384 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14016) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14016 (by decide)
  decide +kernel

theorem h14016 : P.leaf 36 14016 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14016_0 (.nil)) (by decide) (by decide))

theorem cover14017 : P.CoversSplit 26 10 14017 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [475]) (by decide +kernel)

theorem c14017_0 : P.sumLeaves 26 14353408 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14017) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14017 (by decide)
  decide +kernel

theorem h14017 : P.leaf 36 14017 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14017_0 (.nil)) (by decide) (by decide))

theorem cover14019 : P.CoversSplit 26 10 14019 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14019_0 : P.sumLeaves 26 14355456 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14019) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14019 (by decide)
  decide +kernel

theorem h14019 : P.leaf 36 14019 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14019_0 (.nil)) (by decide) (by decide))

theorem cover14021 : P.CoversSplit 26 10 14021 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [475]) (by decide +kernel)

theorem c14021_0 : P.sumLeaves 26 14357504 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14021) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14021 (by decide)
  decide +kernel

theorem h14021 : P.leaf 36 14021 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14021_0 (.nil)) (by decide) (by decide))

theorem cover14022 : P.CoversSplit 26 10 14022 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14022_0 : P.sumLeaves 26 14358528 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14022) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14022 (by decide)
  decide +kernel

theorem h14022 : P.leaf 36 14022 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14022_0 (.nil)) (by decide) (by decide))

theorem cover14023 : P.CoversSplit 26 10 14023 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14023_0 : P.sumLeaves 26 14359552 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14023) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14023 (by decide)
  decide +kernel

theorem h14023 : P.leaf 36 14023 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14023_0 (.nil)) (by decide) (by decide))

theorem cover14031 : P.CoversSplit 26 10 14031 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14031_0 : P.sumLeaves 26 14367744 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14031) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14031 (by decide)
  decide +kernel

theorem h14031 : P.leaf 36 14031 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14031_0 (.nil)) (by decide) (by decide))

theorem cover14032 : P.CoversSplit 26 10 14032 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [467]) (by decide +kernel)

theorem c14032_0 : P.sumLeaves 26 14368768 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14032) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14032 (by decide)
  decide +kernel

theorem h14032 : P.leaf 36 14032 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14032_0 (.nil)) (by decide) (by decide))

theorem cover14033 : P.CoversSplit 26 10 14033 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [475]) (by decide +kernel)

theorem c14033_0 : P.sumLeaves 26 14369792 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14033) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14033 (by decide)
  decide +kernel

theorem h14033 : P.leaf 36 14033 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14033_0 (.nil)) (by decide) (by decide))

theorem cover14035 : P.CoversSplit 26 10 14035 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c14035_0 : P.sumLeaves 26 14371840 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14035) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14035 (by decide)
  decide +kernel

theorem h14035 : P.leaf 36 14035 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14035_0 (.nil)) (by decide) (by decide))

theorem cover14036 : P.CoversSplit 26 10 14036 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [475]) (by decide +kernel)

theorem c14036_0 : P.sumLeaves 26 14372864 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14036) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14036 (by decide)
  decide +kernel

theorem h14036 : P.leaf 36 14036 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14036_0 (.nil)) (by decide) (by decide))

theorem cover14037 : P.CoversSplit 26 10 14037 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [475]) (by decide +kernel)

theorem c14037_0 : P.sumLeaves 26 14373888 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14037) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14037 (by decide)
  decide +kernel

theorem h14037 : P.leaf 36 14037 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14037_0 (.nil)) (by decide) (by decide))

theorem cover14038 : P.CoversSplit 26 10 14038 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c14038_0 : P.sumLeaves 26 14374912 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14038) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14038 (by decide)
  decide +kernel

theorem h14038 : P.leaf 36 14038 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14038_0 (.nil)) (by decide) (by decide))

theorem cover14039 : P.CoversSplit 26 10 14039 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c14039_0 : P.sumLeaves 26 14375936 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14039) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14039 (by decide)
  decide +kernel

theorem h14039 : P.leaf 36 14039 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14039_0 (.nil)) (by decide) (by decide))

theorem cover14044 : P.CoversSplit 26 10 14044 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c14044_0 : P.sumLeaves 26 14381056 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14044) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14044 (by decide)
  decide +kernel

theorem h14044 : P.leaf 36 14044 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14044_0 (.nil)) (by decide) (by decide))

theorem cover14045 : P.CoversSplit 26 10 14045 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c14045_0 : P.sumLeaves 26 14382080 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14045) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14045 (by decide)
  decide +kernel

theorem h14045 : P.leaf 36 14045 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14045_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(13951, 720), (14001, 360), (14002, 720), (14003, 720), (14004, 360), (14005, 720), (14006, 720), (14007, 720), (14008, 720), (14009, 720), (14010, 720), (14011, 720), (14012, 720), (14013, 720), (14014, 720), (14015, 720), (14016, 60), (14017, 720), (14019, 360), (14021, 360), (14022, 360), (14023, 720), (14031, 180), (14032, 120), (14033, 720), (14035, 360), (14036, 720), (14037, 720), (14038, 720), (14039, 720), (14044, 360), (14045, 720)]

theorem segOK : checkSeg 20 perms 13951 14047 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 13951 14047 18720 0 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 0)
    (SegSum.cons (w := 720) h13951 (SegSum.cons (w := 360) h14001 (SegSum.cons (w := 720) h14002 (SegSum.cons (w := 720) h14003 (SegSum.cons (w := 360) h14004 (SegSum.cons (w := 720) h14005 (SegSum.cons (w := 720) h14006 (SegSum.cons (w := 720) h14007 (SegSum.cons (w := 720) h14008 (SegSum.cons (w := 720) h14009 (SegSum.cons (w := 720) h14010 (SegSum.cons (w := 720) h14011 (SegSum.cons (w := 720) h14012 (SegSum.cons (w := 720) h14013 (SegSum.cons (w := 720) h14014 (SegSum.cons (w := 720) h14015 (SegSum.cons (w := 60) h14016 (SegSum.cons (w := 720) h14017 (SegSum.cons (w := 360) h14019 (SegSum.cons (w := 360) h14021 (SegSum.cons (w := 360) h14022 (SegSum.cons (w := 720) h14023 (SegSum.cons (w := 180) h14031 (SegSum.cons (w := 120) h14032 (SegSum.cons (w := 720) h14033 (SegSum.cons (w := 360) h14035 (SegSum.cons (w := 720) h14036 (SegSum.cons (w := 720) h14037 (SegSum.cons (w := 720) h14038 (SegSum.cons (w := 720) h14039 (SegSum.cons (w := 360) h14044 (SegSum.cons (w := 720) h14045 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S26
