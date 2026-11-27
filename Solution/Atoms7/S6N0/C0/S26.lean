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

namespace RACert.S6N0.C0.S26

open RACert RACert.Problem

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

theorem cover14047 : P.CoversSplit 26 10 14047 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c14047_0 : P.sumLeaves 26 14384128 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14047) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14047 (by decide)
  decide +kernel

theorem h14047 : P.leaf 36 14047 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14047_0 (.nil)) (by decide) (by decide))

theorem cover14049 : P.CoversSplit 26 10 14049 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [475]) (by decide +kernel)

theorem c14049_0 : P.sumLeaves 26 14386176 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14049) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14049 (by decide)
  decide +kernel

theorem h14049 : P.leaf 36 14049 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14049_0 (.nil)) (by decide) (by decide))

theorem cover14050 : P.CoversSplit 26 10 14050 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14050_0 : P.sumLeaves 26 14387200 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14050) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14050 (by decide)
  decide +kernel

theorem h14050 : P.leaf 36 14050 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14050_0 (.nil)) (by decide) (by decide))

theorem cover14051 : P.CoversSplit 26 10 14051 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14051_0 : P.sumLeaves 26 14388224 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14051) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14051 (by decide)
  decide +kernel

theorem h14051 : P.leaf 36 14051 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14051_0 (.nil)) (by decide) (by decide))

theorem cover14052 : P.CoversSplit 26 10 14052 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [475]) (by decide +kernel)

theorem c14052_0 : P.sumLeaves 26 14389248 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14052) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14052 (by decide)
  decide +kernel

theorem h14052 : P.leaf 36 14052 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14052_0 (.nil)) (by decide) (by decide))

theorem cover14053 : P.CoversSplit 26 10 14053 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [475]) (by decide +kernel)

theorem c14053_0 : P.sumLeaves 26 14390272 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14053) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14053 (by decide)
  decide +kernel

theorem h14053 : P.leaf 36 14053 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14053_0 (.nil)) (by decide) (by decide))

theorem cover14054 : P.CoversSplit 26 10 14054 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14054_0 : P.sumLeaves 26 14391296 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14054) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14054 (by decide)
  decide +kernel

theorem h14054 : P.leaf 36 14054 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14054_0 (.nil)) (by decide) (by decide))

theorem cover14055 : P.CoversSplit 26 10 14055 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14055_0 : P.sumLeaves 26 14392320 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14055) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14055 (by decide)
  decide +kernel

theorem h14055 : P.leaf 36 14055 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14055_0 (.nil)) (by decide) (by decide))

theorem cover14056 : P.CoversSplit 26 10 14056 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14056_0 : P.sumLeaves 26 14393344 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14056) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14056 (by decide)
  decide +kernel

theorem h14056 : P.leaf 36 14056 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14056_0 (.nil)) (by decide) (by decide))

theorem cover14057 : P.CoversSplit 26 10 14057 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14057_0 : P.sumLeaves 26 14394368 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14057) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14057 (by decide)
  decide +kernel

theorem h14057 : P.leaf 36 14057 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14057_0 (.nil)) (by decide) (by decide))

theorem cover14058 : P.CoversSplit 26 10 14058 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14058_0 : P.sumLeaves 26 14395392 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14058) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14058 (by decide)
  decide +kernel

theorem h14058 : P.leaf 36 14058 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14058_0 (.nil)) (by decide) (by decide))

theorem cover14059 : P.CoversSplit 26 10 14059 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14059_0 : P.sumLeaves 26 14396416 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14059) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14059 (by decide)
  decide +kernel

theorem h14059 : P.leaf 36 14059 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14059_0 (.nil)) (by decide) (by decide))

theorem cover14060 : P.CoversSplit 26 10 14060 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14060_0 : P.sumLeaves 26 14397440 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14060) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14060 (by decide)
  decide +kernel

theorem h14060 : P.leaf 36 14060 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14060_0 (.nil)) (by decide) (by decide))

theorem cover14061 : P.CoversSplit 26 10 14061 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14061_0 : P.sumLeaves 26 14398464 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14061) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14061 (by decide)
  decide +kernel

theorem h14061 : P.leaf 36 14061 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14061_0 (.nil)) (by decide) (by decide))

theorem cover14062 : P.CoversSplit 26 10 14062 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14062_0 : P.sumLeaves 26 14399488 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14062) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14062 (by decide)
  decide +kernel

theorem h14062 : P.leaf 36 14062 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14062_0 (.nil)) (by decide) (by decide))

theorem cover14063 : P.CoversSplit 26 10 14063 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14063_0 : P.sumLeaves 26 14400512 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14063) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14063 (by decide)
  decide +kernel

theorem h14063 : P.leaf 36 14063 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14063_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(14016, 60), (14017, 720), (14019, 360), (14021, 360), (14022, 360), (14023, 720), (14031, 180), (14032, 120), (14033, 720), (14035, 360), (14036, 720), (14037, 720), (14038, 720), (14039, 720), (14044, 360), (14045, 720), (14047, 360), (14049, 360), (14050, 720), (14051, 720), (14052, 360), (14053, 720), (14054, 720), (14055, 720), (14056, 720), (14057, 720), (14058, 720), (14059, 720), (14060, 720), (14061, 720), (14062, 720), (14063, 720)]

theorem segOK : checkSeg 20 perms 14016 14065 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 14016 14065 18360 0 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 0)
    (SegSum.cons (w := 60) h14016 (SegSum.cons (w := 720) h14017 (SegSum.cons (w := 360) h14019 (SegSum.cons (w := 360) h14021 (SegSum.cons (w := 360) h14022 (SegSum.cons (w := 720) h14023 (SegSum.cons (w := 180) h14031 (SegSum.cons (w := 120) h14032 (SegSum.cons (w := 720) h14033 (SegSum.cons (w := 360) h14035 (SegSum.cons (w := 720) h14036 (SegSum.cons (w := 720) h14037 (SegSum.cons (w := 720) h14038 (SegSum.cons (w := 720) h14039 (SegSum.cons (w := 360) h14044 (SegSum.cons (w := 720) h14045 (SegSum.cons (w := 360) h14047 (SegSum.cons (w := 360) h14049 (SegSum.cons (w := 720) h14050 (SegSum.cons (w := 720) h14051 (SegSum.cons (w := 360) h14052 (SegSum.cons (w := 720) h14053 (SegSum.cons (w := 720) h14054 (SegSum.cons (w := 720) h14055 (SegSum.cons (w := 720) h14056 (SegSum.cons (w := 720) h14057 (SegSum.cons (w := 720) h14058 (SegSum.cons (w := 720) h14059 (SegSum.cons (w := 720) h14060 (SegSum.cons (w := 720) h14061 (SegSum.cons (w := 720) h14062 (SegSum.cons (w := 720) h14063 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S26
