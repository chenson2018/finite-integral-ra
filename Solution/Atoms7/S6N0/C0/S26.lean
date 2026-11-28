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

theorem h14016 : P.leaf 36 14016 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14016) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14016) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14016 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14017 : P.CoversSplit 26 10 14017 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [475]) (by decide +kernel)

theorem h14017 : P.leaf 36 14017 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14017) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14017) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14017 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14019 : P.CoversSplit 26 10 14019 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h14019 : P.leaf 36 14019 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14019) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14019) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14019 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14021 : P.CoversSplit 26 10 14021 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [475]) (by decide +kernel)

theorem h14021 : P.leaf 36 14021 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14021) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14021) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14021 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14022 : P.CoversSplit 26 10 14022 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h14022 : P.leaf 36 14022 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14022) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14022) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14022 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14023 : P.CoversSplit 26 10 14023 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h14023 : P.leaf 36 14023 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14023) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14023) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14023 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14031 : P.CoversSplit 26 10 14031 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h14031 : P.leaf 36 14031 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14031) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14031) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14031 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14032 : P.CoversSplit 26 10 14032 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [467]) (by decide +kernel)

theorem h14032 : P.leaf 36 14032 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14032) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14032) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14032 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14033 : P.CoversSplit 26 10 14033 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [475]) (by decide +kernel)

theorem h14033 : P.leaf 36 14033 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14033) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14033) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14033 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14035 : P.CoversSplit 26 10 14035 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h14035 : P.leaf 36 14035 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14035) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14035) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14035 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14036 : P.CoversSplit 26 10 14036 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [475]) (by decide +kernel)

theorem h14036 : P.leaf 36 14036 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14036) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14036) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14036 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14037 : P.CoversSplit 26 10 14037 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [475]) (by decide +kernel)

theorem h14037 : P.leaf 36 14037 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14037) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14037) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14037 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14038 : P.CoversSplit 26 10 14038 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h14038 : P.leaf 36 14038 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14038) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14038) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14038 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14039 : P.CoversSplit 26 10 14039 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h14039 : P.leaf 36 14039 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14039) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14039) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14039 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14044 : P.CoversSplit 26 10 14044 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h14044 : P.leaf 36 14044 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14044) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14044) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14044 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14045 : P.CoversSplit 26 10 14045 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h14045 : P.leaf 36 14045 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14045) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14045) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14045 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14047 : P.CoversSplit 26 10 14047 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h14047 : P.leaf 36 14047 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14047) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14047) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14047 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14049 : P.CoversSplit 26 10 14049 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [475]) (by decide +kernel)

theorem h14049 : P.leaf 36 14049 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14049) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14049) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14049 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14050 : P.CoversSplit 26 10 14050 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h14050 : P.leaf 36 14050 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14050) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14050) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14050 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14051 : P.CoversSplit 26 10 14051 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h14051 : P.leaf 36 14051 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14051) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14051) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14051 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14052 : P.CoversSplit 26 10 14052 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [475]) (by decide +kernel)

theorem h14052 : P.leaf 36 14052 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14052) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14052) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14052 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14053 : P.CoversSplit 26 10 14053 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [475]) (by decide +kernel)

theorem h14053 : P.leaf 36 14053 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14053) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14053) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14053 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14054 : P.CoversSplit 26 10 14054 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h14054 : P.leaf 36 14054 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14054) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14054) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14054 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14055 : P.CoversSplit 26 10 14055 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h14055 : P.leaf 36 14055 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14055) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14055) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14055 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14056 : P.CoversSplit 26 10 14056 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h14056 : P.leaf 36 14056 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14056) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14056) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14056 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14057 : P.CoversSplit 26 10 14057 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h14057 : P.leaf 36 14057 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14057) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14057) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14057 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14058 : P.CoversSplit 26 10 14058 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h14058 : P.leaf 36 14058 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14058) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14058) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14058 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14059 : P.CoversSplit 26 10 14059 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h14059 : P.leaf 36 14059 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14059) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14059) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14059 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14060 : P.CoversSplit 26 10 14060 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h14060 : P.leaf 36 14060 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14060) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14060) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14060 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14061 : P.CoversSplit 26 10 14061 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h14061 : P.leaf 36 14061 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14061) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14061) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14061 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14062 : P.CoversSplit 26 10 14062 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h14062 : P.leaf 36 14062 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14062) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14062) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14062 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14063 : P.CoversSplit 26 10 14063 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h14063 : P.leaf 36 14063 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14063) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14063) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14063 (by decide) (by decide) (by decide +kernel)
  decide +kernel

def seg : List (ℕ × ℕ) := [(14016, 60), (14017, 720), (14019, 360), (14021, 360), (14022, 360), (14023, 720), (14031, 180), (14032, 120), (14033, 720), (14035, 360), (14036, 720), (14037, 720), (14038, 720), (14039, 720), (14044, 360), (14045, 720), (14047, 360), (14049, 360), (14050, 720), (14051, 720), (14052, 360), (14053, 720), (14054, 720), (14055, 720), (14056, 720), (14057, 720), (14058, 720), (14059, 720), (14060, 720), (14061, 720), (14062, 720), (14063, 720)]

theorem segOK : checkSeg 20 perms 14016 14065 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 14016 14065 18360 0 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 0)
    (SegSum.cons (w := 60) h14016 (SegSum.cons (w := 720) h14017 (SegSum.cons (w := 360) h14019 (SegSum.cons (w := 360) h14021 (SegSum.cons (w := 360) h14022 (SegSum.cons (w := 720) h14023 (SegSum.cons (w := 180) h14031 (SegSum.cons (w := 120) h14032 (SegSum.cons (w := 720) h14033 (SegSum.cons (w := 360) h14035 (SegSum.cons (w := 720) h14036 (SegSum.cons (w := 720) h14037 (SegSum.cons (w := 720) h14038 (SegSum.cons (w := 720) h14039 (SegSum.cons (w := 360) h14044 (SegSum.cons (w := 720) h14045 (SegSum.cons (w := 360) h14047 (SegSum.cons (w := 360) h14049 (SegSum.cons (w := 720) h14050 (SegSum.cons (w := 720) h14051 (SegSum.cons (w := 360) h14052 (SegSum.cons (w := 720) h14053 (SegSum.cons (w := 720) h14054 (SegSum.cons (w := 720) h14055 (SegSum.cons (w := 720) h14056 (SegSum.cons (w := 720) h14057 (SegSum.cons (w := 720) h14058 (SegSum.cons (w := 720) h14059 (SegSum.cons (w := 720) h14060 (SegSum.cons (w := 720) h14061 (SegSum.cons (w := 720) h14062 (SegSum.cons (w := 720) h14063 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S26
