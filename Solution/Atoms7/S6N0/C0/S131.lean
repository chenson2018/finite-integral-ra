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

namespace RACert.S6N0.C0.S131

open RACert RACert.Problem

theorem cover243711 : P.CoversSplit 26 10 243711 0xfffffffffffffffffffffffffffffafaffffffffffffccccffffaaaaffcc8888ffffffffffffffffffffaaaaffffaaaaffffffffffffccccffffaaaaffcc8888fffffffffffffffffffffffffffffafaffffffffccccccccffffaaaacccc8888ffffffffffffffffffffaaaaffffaaaaffffffffccccccccffffaaaacccc8888 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c243711_0 : P.sumLeaves 26 249560064 148 = 486157596 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243711) (lo := 0) (len := 148) (W := 486157596) check rows elimOK (by decide) (by decide) cover243711 (by decide)
  decide +kernel

theorem c243711_1 : P.sumLeaves 26 249560212 104 = 694609328 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243711) (lo := 148) (len := 104) (W := 694609328) check rows elimOK (by decide) (by decide) cover243711 (by decide)
  decide +kernel

theorem c243711_2 : P.sumLeaves 26 249560316 144 = 917866659 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243711) (lo := 252) (len := 144) (W := 917866659) check rows elimOK (by decide) (by decide) cover243711 (by decide)
  decide +kernel

theorem c243711_3 : P.sumLeaves 26 249560460 96 = 1276381720 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243711) (lo := 396) (len := 96) (W := 1276381720) check rows elimOK (by decide) (by decide) cover243711 (by decide)
  decide +kernel

theorem c243711_4 : P.sumLeaves 26 249560556 128 = 1117914149 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243711) (lo := 492) (len := 128) (W := 1117914149) check rows elimOK (by decide) (by decide) cover243711 (by decide)
  decide +kernel

theorem c243711_5 : P.sumLeaves 26 249560684 112 = 1230642400 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243711) (lo := 620) (len := 112) (W := 1230642400) check rows elimOK (by decide) (by decide) cover243711 (by decide)
  decide +kernel

theorem c243711_6 : P.sumLeaves 26 249560796 128 = 1401835464 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243711) (lo := 732) (len := 128) (W := 1401835464) check rows elimOK (by decide) (by decide) cover243711 (by decide)
  decide +kernel

theorem c243711_7 : P.sumLeaves 26 249560924 100 = 1497983911 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243711) (lo := 860) (len := 100) (W := 1497983911) check rows elimOK (by decide) (by decide) cover243711 (by decide)
  decide +kernel

theorem c243711_8 : P.sumLeaves 26 249561024 64 = 1271367316 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243711) (lo := 960) (len := 64) (W := 1271367316) check rows elimOK (by decide) (by decide) cover243711 (by decide)
  decide +kernel

theorem h243711 : P.leaf 36 243711 = 9894758543 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(148, 486157596), (104, 694609328), (144, 917866659), (96, 1276381720), (128, 1117914149), (112, 1230642400), (128, 1401835464), (100, 1497983911), (64, 1271367316)]) (.cons c243711_0 (.cons c243711_1 (.cons c243711_2 (.cons c243711_3 (.cons c243711_4 (.cons c243711_5 (.cons c243711_6 (.cons c243711_7 (.cons c243711_8 (.nil)))))))))) (by decide) (by decide))

theorem cover245630 : P.CoversSplit 26 10 245630 0xfffffffffffffffffffffffffffffafaffffffffffffffccffffaaaaff00aa00ffffffffffffffffffffaaaaffffaaaaffffffffffffffccffffaaaaff00aa00fffffffffffffffffffffffffffffafaffffffffff00ff00ffffaaaaff00aa00ffffffffffffffffffffaaaaffffaaaaffffffffff00ff00ffffaaaaff00aa00 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c245630_0 : P.sumLeaves 26 251525120 148 = 111158896 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245630) (lo := 0) (len := 148) (W := 111158896) check rows elimOK (by decide) (by decide) cover245630 (by decide)
  decide +kernel

theorem c245630_1 : P.sumLeaves 26 251525268 104 = 179733552 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245630) (lo := 148) (len := 104) (W := 179733552) check rows elimOK (by decide) (by decide) cover245630 (by decide)
  decide +kernel

theorem c245630_2 : P.sumLeaves 26 251525372 144 = 476520882 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245630) (lo := 252) (len := 144) (W := 476520882) check rows elimOK (by decide) (by decide) cover245630 (by decide)
  decide +kernel

theorem c245630_3 : P.sumLeaves 26 251525516 96 = 926613575 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245630) (lo := 396) (len := 96) (W := 926613575) check rows elimOK (by decide) (by decide) cover245630 (by decide)
  decide +kernel

theorem c245630_4 : P.sumLeaves 26 251525612 128 = 772536286 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245630) (lo := 492) (len := 128) (W := 772536286) check rows elimOK (by decide) (by decide) cover245630 (by decide)
  decide +kernel

theorem c245630_5 : P.sumLeaves 26 251525740 112 = 794302305 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245630) (lo := 620) (len := 112) (W := 794302305) check rows elimOK (by decide) (by decide) cover245630 (by decide)
  decide +kernel

theorem c245630_6 : P.sumLeaves 26 251525852 128 = 998194723 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245630) (lo := 732) (len := 128) (W := 998194723) check rows elimOK (by decide) (by decide) cover245630 (by decide)
  decide +kernel

theorem c245630_7 : P.sumLeaves 26 251525980 100 = 1025730733 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245630) (lo := 860) (len := 100) (W := 1025730733) check rows elimOK (by decide) (by decide) cover245630 (by decide)
  decide +kernel

theorem c245630_8 : P.sumLeaves 26 251526080 64 = 1135286926 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245630) (lo := 960) (len := 64) (W := 1135286926) check rows elimOK (by decide) (by decide) cover245630 (by decide)
  decide +kernel

theorem h245630 : P.leaf 36 245630 = 6420077878 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(148, 111158896), (104, 179733552), (144, 476520882), (96, 926613575), (128, 772536286), (112, 794302305), (128, 998194723), (100, 1025730733), (64, 1135286926)]) (.cons c245630_0 (.cons c245630_1 (.cons c245630_2 (.cons c245630_3 (.cons c245630_4 (.cons c245630_5 (.cons c245630_6 (.cons c245630_7 (.cons c245630_8 (.nil)))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(243711, 360), (245630, 120)]

theorem segOK : checkSeg 20 perms 243711 245631 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 243711 245631 480 4332522420840 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 4332522420840)
    (SegSum.cons (w := 360) h243711 (SegSum.cons (w := 120) h245630 (show SegSum (P.leaf 36) [] 0 from rfl))) (by decide)

end RACert.S6N0.C0.S131
