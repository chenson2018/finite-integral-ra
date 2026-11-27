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

namespace RACert.S6N0.C0.S130

open RACert RACert.Problem

theorem cover243708 : P.CoversSplit 26 10 243708 0xfffffffffffffffffffffffffffffafaffffffffffffccccffffaaaaffcc8888ffffffffffffffffffffa0a0ffffa0a0ffffffffffffccccffffa0a0ffcc8080fffffffffffffffffffffffffffffafaffffffffcc00cc00ffffaaaacc008800ffffffffffffffffffffa0a0ffffa0a0ffffffffcc00cc00ffffa0a0cc008000 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c243708_0 : P.sumLeaves 26 249556992 183 = 24203020 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243708) (lo := 0) (len := 183) (W := 24203020) check rows elimOK (by decide) (by decide) cover243708 (by decide)
  decide +kernel

theorem c243708_1 : P.sumLeaves 26 249557175 130 = 51002726 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243708) (lo := 183) (len := 130) (W := 51002726) check rows elimOK (by decide) (by decide) cover243708 (by decide)
  decide +kernel

theorem c243708_2 : P.sumLeaves 26 249557305 124 = 162834275 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243708) (lo := 313) (len := 124) (W := 162834275) check rows elimOK (by decide) (by decide) cover243708 (by decide)
  decide +kernel

theorem c243708_3 : P.sumLeaves 26 249557429 126 = 263749090 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243708) (lo := 437) (len := 126) (W := 263749090) check rows elimOK (by decide) (by decide) cover243708 (by decide)
  decide +kernel

theorem c243708_4 : P.sumLeaves 26 249557555 128 = 165710043 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243708) (lo := 563) (len := 128) (W := 165710043) check rows elimOK (by decide) (by decide) cover243708 (by decide)
  decide +kernel

theorem c243708_5 : P.sumLeaves 26 249557683 116 = 287974016 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243708) (lo := 691) (len := 116) (W := 287974016) check rows elimOK (by decide) (by decide) cover243708 (by decide)
  decide +kernel

theorem c243708_6 : P.sumLeaves 26 249557799 112 = 308907572 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243708) (lo := 807) (len := 112) (W := 308907572) check rows elimOK (by decide) (by decide) cover243708 (by decide)
  decide +kernel

theorem c243708_7 : P.sumLeaves 26 249557911 96 = 595295148 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243708) (lo := 919) (len := 96) (W := 595295148) check rows elimOK (by decide) (by decide) cover243708 (by decide)
  decide +kernel

theorem c243708_8 : P.sumLeaves 26 249558007 9 = 114150972 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243708) (lo := 1015) (len := 9) (W := 114150972) check rows elimOK (by decide) (by decide) cover243708 (by decide)
  decide +kernel

theorem h243708 : P.leaf 36 243708 = 1973826862 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(183, 24203020), (130, 51002726), (124, 162834275), (126, 263749090), (128, 165710043), (116, 287974016), (112, 308907572), (96, 595295148), (9, 114150972)]) (.cons c243708_0 (.cons c243708_1 (.cons c243708_2 (.cons c243708_3 (.cons c243708_4 (.cons c243708_5 (.cons c243708_6 (.cons c243708_7 (.cons c243708_8 (.nil)))))))))) (by decide) (by decide))

theorem cover243709 : P.CoversSplit 26 10 243709 0xfffffffffffffffffffffffffffffafaffffffffffffccccffffaaaaffcc8888ffffffffffffffffffffaaaaffffaaaaffffffffffffccccffffaaaaffcc8888fffffffffffffffffffffffffffffafaffffffffcc00cc00ffffaaaacc008800ffffffffffffffffffffaaaaffffaaaaffffffffcc00cc00ffffaaaacc008800 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c243709_0 : P.sumLeaves 26 249558016 165 = 118761997 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243709) (lo := 0) (len := 165) (W := 118761997) check rows elimOK (by decide) (by decide) cover243709 (by decide)
  decide +kernel

theorem c243709_1 : P.sumLeaves 26 249558181 132 = 180190774 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243709) (lo := 165) (len := 132) (W := 180190774) check rows elimOK (by decide) (by decide) cover243709 (by decide)
  decide +kernel

theorem c243709_2 : P.sumLeaves 26 249558313 127 = 514839702 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243709) (lo := 297) (len := 127) (W := 514839702) check rows elimOK (by decide) (by decide) cover243709 (by decide)
  decide +kernel

theorem c243709_3 : P.sumLeaves 26 249558440 112 = 781326094 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243709) (lo := 424) (len := 112) (W := 781326094) check rows elimOK (by decide) (by decide) cover243709 (by decide)
  decide +kernel

theorem c243709_4 : P.sumLeaves 26 249558552 120 = 371688620 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243709) (lo := 536) (len := 120) (W := 371688620) check rows elimOK (by decide) (by decide) cover243709 (by decide)
  decide +kernel

theorem c243709_5 : P.sumLeaves 26 249558672 104 = 486466776 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243709) (lo := 656) (len := 104) (W := 486466776) check rows elimOK (by decide) (by decide) cover243709 (by decide)
  decide +kernel

theorem c243709_6 : P.sumLeaves 26 249558776 128 = 730915741 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243709) (lo := 760) (len := 128) (W := 730915741) check rows elimOK (by decide) (by decide) cover243709 (by decide)
  decide +kernel

theorem c243709_7 : P.sumLeaves 26 249558904 100 = 930121578 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243709) (lo := 888) (len := 100) (W := 930121578) check rows elimOK (by decide) (by decide) cover243709 (by decide)
  decide +kernel

theorem c243709_8 : P.sumLeaves 26 249559004 36 = 455787674 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243709) (lo := 988) (len := 36) (W := 455787674) check rows elimOK (by decide) (by decide) cover243709 (by decide)
  decide +kernel

theorem h243709 : P.leaf 36 243709 = 4570098956 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(165, 118761997), (132, 180190774), (127, 514839702), (112, 781326094), (120, 371688620), (104, 486466776), (128, 730915741), (100, 930121578), (36, 455787674)]) (.cons c243709_0 (.cons c243709_1 (.cons c243709_2 (.cons c243709_3 (.cons c243709_4 (.cons c243709_5 (.cons c243709_6 (.cons c243709_7 (.cons c243709_8 (.nil)))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(243708, 360), (243709, 720)]

theorem segOK : checkSeg 20 perms 243708 243711 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 243708 243711 1080 4001048918640 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 4001048918640)
    (SegSum.cons (w := 360) h243708 (SegSum.cons (w := 720) h243709 (show SegSum (P.leaf 36) [] 0 from rfl))) (by decide)

end RACert.S6N0.C0.S130
