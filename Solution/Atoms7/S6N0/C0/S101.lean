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

namespace RACert.S6N0.C0.S101

open RACert RACert.Problem

theorem cover122867 : P.CoversSplit 26 10 122867 0xfffffffffffffafafffffafafffffafaffffffffffccfac8fafafafac8c8c8c8fffffafafffffafafafafafafafafafafffffafaffccfac8fafafafac8c8c8c8fffffffffffffafafffffafafffffafaffffffffccccc8c8fafafafac8c8c8c8fffffafafffffafafafafafafafafafafffffafaccccc8c8fafafafac8c8c8c8 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 1315, 1658, 1665]) (by decide +kernel)

theorem c122867_0 : P.sumLeaves 26 125815808 153 = 39877161 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122867) (lo := 0) (len := 153) (W := 39877161) check rows elimOK (by decide) (by decide) cover122867 (by decide)
  decide +kernel

theorem c122867_1 : P.sumLeaves 26 125815961 133 = 54659888 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122867) (lo := 153) (len := 133) (W := 54659888) check rows elimOK (by decide) (by decide) cover122867 (by decide)
  decide +kernel

theorem c122867_2 : P.sumLeaves 26 125816094 126 = 171717439 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122867) (lo := 286) (len := 126) (W := 171717439) check rows elimOK (by decide) (by decide) cover122867 (by decide)
  decide +kernel

theorem c122867_3 : P.sumLeaves 26 125816220 114 = 365891176 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122867) (lo := 412) (len := 114) (W := 365891176) check rows elimOK (by decide) (by decide) cover122867 (by decide)
  decide +kernel

theorem c122867_4 : P.sumLeaves 26 125816334 135 = 172566357 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122867) (lo := 526) (len := 135) (W := 172566357) check rows elimOK (by decide) (by decide) cover122867 (by decide)
  decide +kernel

theorem c122867_5 : P.sumLeaves 26 125816469 129 = 416417814 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122867) (lo := 661) (len := 129) (W := 416417814) check rows elimOK (by decide) (by decide) cover122867 (by decide)
  decide +kernel

theorem c122867_6 : P.sumLeaves 26 125816598 124 = 259690346 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122867) (lo := 790) (len := 124) (W := 259690346) check rows elimOK (by decide) (by decide) cover122867 (by decide)
  decide +kernel

theorem c122867_7 : P.sumLeaves 26 125816722 104 = 553758285 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122867) (lo := 914) (len := 104) (W := 553758285) check rows elimOK (by decide) (by decide) cover122867 (by decide)
  decide +kernel

theorem c122867_8 : P.sumLeaves 26 125816826 6 = 73060270 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122867) (lo := 1018) (len := 6) (W := 73060270) check rows elimOK (by decide) (by decide) cover122867 (by decide)
  decide +kernel

theorem h122867 : P.leaf 36 122867 = 2107638736 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(153, 39877161), (133, 54659888), (126, 171717439), (114, 365891176), (135, 172566357), (129, 416417814), (124, 259690346), (104, 553758285), (6, 73060270)]) (.cons c122867_0 (.cons c122867_1 (.cons c122867_2 (.cons c122867_3 (.cons c122867_4 (.cons c122867_5 (.cons c122867_6 (.cons c122867_7 (.cons c122867_8 (.nil)))))))))) (by decide) (by decide))

theorem cover122870 : P.CoversSplit 26 10 122870 0xfffffffffffffafafffffffffffffafafffffffffffffac8fafafafac8c8c8c8fffffafafffffafafafafafafafafafafffffafafffffac8fafafafac8c8c8c8fffffffffffffafafffffffffffffafaffccffccccccc8c8fac8fac8c8c8c8c8fffffafafffffafafafafafafafafafaffccfac8ccccc8c8fac8fac8c8c8c8c8 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 922, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c122870_0 : P.sumLeaves 26 125818880 171 = 39289168 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122870) (lo := 0) (len := 171) (W := 39289168) check rows elimOK (by decide) (by decide) cover122870 (by decide)
  decide +kernel

theorem c122870_1 : P.sumLeaves 26 125819051 140 = 83310705 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122870) (lo := 171) (len := 140) (W := 83310705) check rows elimOK (by decide) (by decide) cover122870 (by decide)
  decide +kernel

theorem c122870_2 : P.sumLeaves 26 125819191 128 = 292298225 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122870) (lo := 311) (len := 128) (W := 292298225) check rows elimOK (by decide) (by decide) cover122870 (by decide)
  decide +kernel

theorem c122870_3 : P.sumLeaves 26 125819319 126 = 454130360 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122870) (lo := 439) (len := 126) (W := 454130360) check rows elimOK (by decide) (by decide) cover122870 (by decide)
  decide +kernel

theorem c122870_4 : P.sumLeaves 26 125819445 121 = 254663834 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122870) (lo := 565) (len := 121) (W := 254663834) check rows elimOK (by decide) (by decide) cover122870 (by decide)
  decide +kernel

theorem c122870_5 : P.sumLeaves 26 125819566 134 = 428734997 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122870) (lo := 686) (len := 134) (W := 428734997) check rows elimOK (by decide) (by decide) cover122870 (by decide)
  decide +kernel

theorem c122870_6 : P.sumLeaves 26 125819700 109 = 368353919 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122870) (lo := 820) (len := 109) (W := 368353919) check rows elimOK (by decide) (by decide) cover122870 (by decide)
  decide +kernel

theorem c122870_7 : P.sumLeaves 26 125819809 95 = 611469890 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122870) (lo := 929) (len := 95) (W := 611469890) check rows elimOK (by decide) (by decide) cover122870 (by decide)
  decide +kernel

theorem h122870 : P.leaf 36 122870 = 2532251098 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(171, 39289168), (140, 83310705), (128, 292298225), (126, 454130360), (121, 254663834), (134, 428734997), (109, 368353919), (95, 611469890)]) (.cons c122870_0 (.cons c122870_1 (.cons c122870_2 (.cons c122870_3 (.cons c122870_4 (.cons c122870_5 (.cons c122870_6 (.cons c122870_7 (.nil))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(122867, 720), (122870, 360)]

theorem segOK : checkSeg 20 perms 122867 122871 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 122867 122871 1080 2429110285200 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 2429110285200)
    (SegSum.cons (w := 720) h122867 (SegSum.cons (w := 360) h122870 (show SegSum (P.leaf 36) [] 0 from rfl))) (by decide)

end RACert.S6N0.C0.S101
