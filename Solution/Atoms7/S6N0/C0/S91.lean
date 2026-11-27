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

namespace RACert.S6N0.C0.S91

open RACert RACert.Problem

theorem cover122874 : P.CoversSplit 26 10 122874 0xfffffffffffffafafffffffffffffafafffffffffffffac8fafafafac8c8c8c8fffffafafffffafafafafafafafafafafffffafafffffac8fafafafac8c8c8c8fffffffffffffafafffffffffffffafaffffffffccccc8c8fafafafac8c8c8c8fffffafafffffafafafafafafafafafafffffafaccccc8c8fafafafac8c8c8c8 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c122874_0 : P.sumLeaves 26 125822976 153 = 33694304 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122874) (lo := 0) (len := 153) (W := 33694304) check rows elimOK (by decide) (by decide) cover122874 (by decide)
  decide +kernel

theorem c122874_1 : P.sumLeaves 26 125823129 133 = 48154336 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122874) (lo := 153) (len := 133) (W := 48154336) check rows elimOK (by decide) (by decide) cover122874 (by decide)
  decide +kernel

theorem c122874_2 : P.sumLeaves 26 125823262 126 = 147907981 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122874) (lo := 286) (len := 126) (W := 147907981) check rows elimOK (by decide) (by decide) cover122874 (by decide)
  decide +kernel

theorem c122874_3 : P.sumLeaves 26 125823388 103 = 409357828 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122874) (lo := 412) (len := 103) (W := 409357828) check rows elimOK (by decide) (by decide) cover122874 (by decide)
  decide +kernel

theorem c122874_4 : P.sumLeaves 26 125823491 136 = 174173856 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122874) (lo := 515) (len := 136) (W := 174173856) check rows elimOK (by decide) (by decide) cover122874 (by decide)
  decide +kernel

theorem c122874_5 : P.sumLeaves 26 125823627 116 = 478171551 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122874) (lo := 651) (len := 116) (W := 478171551) check rows elimOK (by decide) (by decide) cover122874 (by decide)
  decide +kernel

theorem c122874_6 : P.sumLeaves 26 125823743 133 = 242810771 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122874) (lo := 767) (len := 133) (W := 242810771) check rows elimOK (by decide) (by decide) cover122874 (by decide)
  decide +kernel

theorem c122874_7 : P.sumLeaves 26 125823876 102 = 473475979 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122874) (lo := 900) (len := 102) (W := 473475979) check rows elimOK (by decide) (by decide) cover122874 (by decide)
  decide +kernel

theorem c122874_8 : P.sumLeaves 26 125823978 22 = 245001056 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122874) (lo := 1002) (len := 22) (W := 245001056) check rows elimOK (by decide) (by decide) cover122874 (by decide)
  decide +kernel

theorem h122874 : P.leaf 36 122874 = 2252747662 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(153, 33694304), (133, 48154336), (126, 147907981), (103, 409357828), (136, 174173856), (116, 478171551), (133, 242810771), (102, 473475979), (22, 245001056)]) (.cons c122874_0 (.cons c122874_1 (.cons c122874_2 (.cons c122874_3 (.cons c122874_4 (.cons c122874_5 (.cons c122874_6 (.cons c122874_7 (.cons c122874_8 (.nil)))))))))) (by decide) (by decide))

theorem cover122875 : P.CoversSplit 26 10 122875 0xfffffffffffffafafffffffffffffafafffffffffffffac8fafafafac8c8c8c8fffffafafffffafafafafafafafafafafffffafafffffac8fafafafac8c8c8c8fffffffffffffafafffffffffffffafaffffffffccccc8c8fafafafac8c8c8c8fffffafafffffafafafafafafafafafafffffafaccccc8c8fafafafac8c8c8c8 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c122875_0 : P.sumLeaves 26 125824000 153 = 162968821 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122875) (lo := 0) (len := 153) (W := 162968821) check rows elimOK (by decide) (by decide) cover122875 (by decide)
  decide +kernel

theorem c122875_1 : P.sumLeaves 26 125824153 133 = 201723547 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122875) (lo := 153) (len := 133) (W := 201723547) check rows elimOK (by decide) (by decide) cover122875 (by decide)
  decide +kernel

theorem c122875_2 : P.sumLeaves 26 125824286 126 = 296565281 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122875) (lo := 286) (len := 126) (W := 296565281) check rows elimOK (by decide) (by decide) cover122875 (by decide)
  decide +kernel

theorem c122875_3 : P.sumLeaves 26 125824412 103 = 567681939 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122875) (lo := 412) (len := 103) (W := 567681939) check rows elimOK (by decide) (by decide) cover122875 (by decide)
  decide +kernel

theorem c122875_4 : P.sumLeaves 26 125824515 136 = 385513917 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122875) (lo := 515) (len := 136) (W := 385513917) check rows elimOK (by decide) (by decide) cover122875 (by decide)
  decide +kernel

theorem c122875_5 : P.sumLeaves 26 125824651 116 = 838427808 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122875) (lo := 651) (len := 116) (W := 838427808) check rows elimOK (by decide) (by decide) cover122875 (by decide)
  decide +kernel

theorem c122875_6 : P.sumLeaves 26 125824767 133 = 484339325 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122875) (lo := 767) (len := 133) (W := 484339325) check rows elimOK (by decide) (by decide) cover122875 (by decide)
  decide +kernel

theorem c122875_7 : P.sumLeaves 26 125824900 102 = 821085577 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122875) (lo := 900) (len := 102) (W := 821085577) check rows elimOK (by decide) (by decide) cover122875 (by decide)
  decide +kernel

theorem c122875_8 : P.sumLeaves 26 125825002 22 = 340035908 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122875) (lo := 1002) (len := 22) (W := 340035908) check rows elimOK (by decide) (by decide) cover122875 (by decide)
  decide +kernel

theorem h122875 : P.leaf 36 122875 = 4098342123 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(153, 162968821), (133, 201723547), (126, 296565281), (103, 567681939), (136, 385513917), (116, 838427808), (133, 484339325), (102, 821085577), (22, 340035908)]) (.cons c122875_0 (.cons c122875_1 (.cons c122875_2 (.cons c122875_3 (.cons c122875_4 (.cons c122875_5 (.cons c122875_6 (.cons c122875_7 (.cons c122875_8 (.nil)))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(122874, 720), (122875, 720)]

theorem segOK : checkSeg 20 perms 122874 122878 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 122874 122878 1440 4572784645200 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 4572784645200)
    (SegSum.cons (w := 720) h122874 (SegSum.cons (w := 720) h122875 (show SegSum (P.leaf 36) [] 0 from rfl))) (by decide)

end RACert.S6N0.C0.S91
