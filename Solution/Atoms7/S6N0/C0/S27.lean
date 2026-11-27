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

namespace RACert.S6N0.C0.S27

open RACert RACert.Problem

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

theorem cover14065 : P.CoversSplit 26 10 14065 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [475]) (by decide +kernel)

theorem c14065_0 : P.sumLeaves 26 14402560 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14065) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14065 (by decide)
  decide +kernel

theorem h14065 : P.leaf 36 14065 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14065_0 (.nil)) (by decide) (by decide))

theorem cover14066 : P.CoversSplit 26 10 14066 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c14066_0 : P.sumLeaves 26 14403584 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14066) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14066 (by decide)
  decide +kernel

theorem h14066 : P.leaf 36 14066 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14066_0 (.nil)) (by decide) (by decide))

theorem cover14067 : P.CoversSplit 26 10 14067 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c14067_0 : P.sumLeaves 26 14404608 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14067) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14067 (by decide)
  decide +kernel

theorem h14067 : P.leaf 36 14067 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14067_0 (.nil)) (by decide) (by decide))

theorem cover14068 : P.CoversSplit 26 10 14068 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [475]) (by decide +kernel)

theorem c14068_0 : P.sumLeaves 26 14405632 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14068) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14068 (by decide)
  decide +kernel

theorem h14068 : P.leaf 36 14068 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14068_0 (.nil)) (by decide) (by decide))

theorem cover14069 : P.CoversSplit 26 10 14069 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [475]) (by decide +kernel)

theorem c14069_0 : P.sumLeaves 26 14406656 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14069) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14069 (by decide)
  decide +kernel

theorem h14069 : P.leaf 36 14069 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14069_0 (.nil)) (by decide) (by decide))

theorem cover14070 : P.CoversSplit 26 10 14070 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c14070_0 : P.sumLeaves 26 14407680 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14070) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14070 (by decide)
  decide +kernel

theorem h14070 : P.leaf 36 14070 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14070_0 (.nil)) (by decide) (by decide))

theorem cover14071 : P.CoversSplit 26 10 14071 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c14071_0 : P.sumLeaves 26 14408704 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14071) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14071 (by decide)
  decide +kernel

theorem h14071 : P.leaf 36 14071 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14071_0 (.nil)) (by decide) (by decide))

theorem cover14072 : P.CoversSplit 26 10 14072 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c14072_0 : P.sumLeaves 26 14409728 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14072) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14072 (by decide)
  decide +kernel

theorem h14072 : P.leaf 36 14072 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14072_0 (.nil)) (by decide) (by decide))

theorem cover14073 : P.CoversSplit 26 10 14073 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c14073_0 : P.sumLeaves 26 14410752 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14073) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14073 (by decide)
  decide +kernel

theorem h14073 : P.leaf 36 14073 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14073_0 (.nil)) (by decide) (by decide))

theorem cover14074 : P.CoversSplit 26 10 14074 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c14074_0 : P.sumLeaves 26 14411776 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14074) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14074 (by decide)
  decide +kernel

theorem h14074 : P.leaf 36 14074 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14074_0 (.nil)) (by decide) (by decide))

theorem cover14075 : P.CoversSplit 26 10 14075 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c14075_0 : P.sumLeaves 26 14412800 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14075) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14075 (by decide)
  decide +kernel

theorem h14075 : P.leaf 36 14075 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14075_0 (.nil)) (by decide) (by decide))

theorem cover14076 : P.CoversSplit 26 10 14076 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c14076_0 : P.sumLeaves 26 14413824 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14076) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14076 (by decide)
  decide +kernel

theorem h14076 : P.leaf 36 14076 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14076_0 (.nil)) (by decide) (by decide))

theorem cover14077 : P.CoversSplit 26 10 14077 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c14077_0 : P.sumLeaves 26 14414848 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14077) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14077 (by decide)
  decide +kernel

theorem h14077 : P.leaf 36 14077 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14077_0 (.nil)) (by decide) (by decide))

theorem cover14078 : P.CoversSplit 26 10 14078 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c14078_0 : P.sumLeaves 26 14415872 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14078) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14078 (by decide)
  decide +kernel

theorem h14078 : P.leaf 36 14078 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14078_0 (.nil)) (by decide) (by decide))

theorem cover14079 : P.CoversSplit 26 10 14079 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c14079_0 : P.sumLeaves 26 14416896 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14079) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14079 (by decide)
  decide +kernel

theorem h14079 : P.leaf 36 14079 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14079_0 (.nil)) (by decide) (by decide))

theorem cover14112 : P.CoversSplit 26 10 14112 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14112_0 : P.sumLeaves 26 14450688 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14112) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14112 (by decide)
  decide +kernel

theorem h14112 : P.leaf 36 14112 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14112_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(14047, 360), (14049, 360), (14050, 720), (14051, 720), (14052, 360), (14053, 720), (14054, 720), (14055, 720), (14056, 720), (14057, 720), (14058, 720), (14059, 720), (14060, 720), (14061, 720), (14062, 720), (14063, 720), (14065, 360), (14066, 720), (14067, 720), (14068, 720), (14069, 720), (14070, 720), (14071, 720), (14072, 720), (14073, 720), (14074, 720), (14075, 720), (14076, 720), (14077, 720), (14078, 720), (14079, 720), (14112, 180)]

theorem segOK : checkSeg 20 perms 14047 14113 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 14047 14113 21060 0 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 0)
    (SegSum.cons (w := 360) h14047 (SegSum.cons (w := 360) h14049 (SegSum.cons (w := 720) h14050 (SegSum.cons (w := 720) h14051 (SegSum.cons (w := 360) h14052 (SegSum.cons (w := 720) h14053 (SegSum.cons (w := 720) h14054 (SegSum.cons (w := 720) h14055 (SegSum.cons (w := 720) h14056 (SegSum.cons (w := 720) h14057 (SegSum.cons (w := 720) h14058 (SegSum.cons (w := 720) h14059 (SegSum.cons (w := 720) h14060 (SegSum.cons (w := 720) h14061 (SegSum.cons (w := 720) h14062 (SegSum.cons (w := 720) h14063 (SegSum.cons (w := 360) h14065 (SegSum.cons (w := 720) h14066 (SegSum.cons (w := 720) h14067 (SegSum.cons (w := 720) h14068 (SegSum.cons (w := 720) h14069 (SegSum.cons (w := 720) h14070 (SegSum.cons (w := 720) h14071 (SegSum.cons (w := 720) h14072 (SegSum.cons (w := 720) h14073 (SegSum.cons (w := 720) h14074 (SegSum.cons (w := 720) h14075 (SegSum.cons (w := 720) h14076 (SegSum.cons (w := 720) h14077 (SegSum.cons (w := 720) h14078 (SegSum.cons (w := 720) h14079 (SegSum.cons (w := 180) h14112 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S27
