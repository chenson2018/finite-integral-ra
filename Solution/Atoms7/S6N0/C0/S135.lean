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

namespace RACert.S6N0.C0.S135

open RACert RACert.Problem

theorem cover245725 : P.CoversSplit 26 10 245725 0xfffffffffffffffffffffffffffffafaffffffffffffff00ffffaaaaffccaa00ffffffffffffffffffffaaaaffffaaaaffffffffffffff00ffffaaaaffccaa00fffffffffffffffffffffffffffffafaffffffffff00ff00ffffaaaaff00aa00ffffffffffffffffffffaaaaffffaaaaffffffffff00ff00ffffaaaaff00aa00 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c245725_0 : P.sumLeaves 26 251622400 148 = 89887020 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245725) (lo := 0) (len := 148) (W := 89887020) check rows elimOK (by decide) (by decide) cover245725 (by decide)
  decide +kernel

theorem c245725_1 : P.sumLeaves 26 251622548 104 = 130957996 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245725) (lo := 148) (len := 104) (W := 130957996) check rows elimOK (by decide) (by decide) cover245725 (by decide)
  decide +kernel

theorem c245725_2 : P.sumLeaves 26 251622652 144 = 392170769 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245725) (lo := 252) (len := 144) (W := 392170769) check rows elimOK (by decide) (by decide) cover245725 (by decide)
  decide +kernel

theorem c245725_3 : P.sumLeaves 26 251622796 96 = 604137238 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245725) (lo := 396) (len := 96) (W := 604137238) check rows elimOK (by decide) (by decide) cover245725 (by decide)
  decide +kernel

theorem c245725_4 : P.sumLeaves 26 251622892 128 = 471407135 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245725) (lo := 492) (len := 128) (W := 471407135) check rows elimOK (by decide) (by decide) cover245725 (by decide)
  decide +kernel

theorem c245725_5 : P.sumLeaves 26 251623020 112 = 430888971 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245725) (lo := 620) (len := 112) (W := 430888971) check rows elimOK (by decide) (by decide) cover245725 (by decide)
  decide +kernel

theorem c245725_6 : P.sumLeaves 26 251623132 128 = 607493211 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245725) (lo := 732) (len := 128) (W := 607493211) check rows elimOK (by decide) (by decide) cover245725 (by decide)
  decide +kernel

theorem c245725_7 : P.sumLeaves 26 251623260 100 = 785881469 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245725) (lo := 860) (len := 100) (W := 785881469) check rows elimOK (by decide) (by decide) cover245725 (by decide)
  decide +kernel

theorem c245725_8 : P.sumLeaves 26 251623360 64 = 682462404 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245725) (lo := 960) (len := 64) (W := 682462404) check rows elimOK (by decide) (by decide) cover245725 (by decide)
  decide +kernel

theorem h245725 : P.leaf 36 245725 = 4195286213 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(148, 89887020), (104, 130957996), (144, 392170769), (96, 604137238), (128, 471407135), (112, 430888971), (128, 607493211), (100, 785881469), (64, 682462404)]) (.cons c245725_0 (.cons c245725_1 (.cons c245725_2 (.cons c245725_3 (.cons c245725_4 (.cons c245725_5 (.cons c245725_6 (.cons c245725_7 (.cons c245725_8 (.nil)))))))))) (by decide) (by decide))

theorem cover245727 : P.CoversSplit 26 10 245727 0xfffffffffffffffffffffffffffffafaffffffffffffff00ffffaaaaffccaa00ffffffffffffffffffffaaaaffffaaaaffffffffffffff00ffffaaaaffccaa00fffffffffffffffffffffffffffffafaffffffffff00ff00ffffaaaaff00aa00ffffffffffffffffffffaaaaffffaaaaffffffffff00ff00ffffaaaaff00aa00 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c245727_0 : P.sumLeaves 26 251624448 148 = 295680983 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245727) (lo := 0) (len := 148) (W := 295680983) check rows elimOK (by decide) (by decide) cover245727 (by decide)
  decide +kernel

theorem c245727_1 : P.sumLeaves 26 251624596 104 = 489999817 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245727) (lo := 148) (len := 104) (W := 489999817) check rows elimOK (by decide) (by decide) cover245727 (by decide)
  decide +kernel

theorem c245727_2 : P.sumLeaves 26 251624700 144 = 611441850 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245727) (lo := 252) (len := 144) (W := 611441850) check rows elimOK (by decide) (by decide) cover245727 (by decide)
  decide +kernel

theorem c245727_3 : P.sumLeaves 26 251624844 96 = 928426832 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245727) (lo := 396) (len := 96) (W := 928426832) check rows elimOK (by decide) (by decide) cover245727 (by decide)
  decide +kernel

theorem c245727_4 : P.sumLeaves 26 251624940 128 = 770848297 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245727) (lo := 492) (len := 128) (W := 770848297) check rows elimOK (by decide) (by decide) cover245727 (by decide)
  decide +kernel

theorem c245727_5 : P.sumLeaves 26 251625068 112 = 880272723 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245727) (lo := 620) (len := 112) (W := 880272723) check rows elimOK (by decide) (by decide) cover245727 (by decide)
  decide +kernel

theorem c245727_6 : P.sumLeaves 26 251625180 128 = 978841016 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245727) (lo := 732) (len := 128) (W := 978841016) check rows elimOK (by decide) (by decide) cover245727 (by decide)
  decide +kernel

theorem c245727_7 : P.sumLeaves 26 251625308 100 = 1072708005 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245727) (lo := 860) (len := 100) (W := 1072708005) check rows elimOK (by decide) (by decide) cover245727 (by decide)
  decide +kernel

theorem c245727_8 : P.sumLeaves 26 251625408 64 = 917023040 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245727) (lo := 960) (len := 64) (W := 917023040) check rows elimOK (by decide) (by decide) cover245727 (by decide)
  decide +kernel

theorem h245727 : P.leaf 36 245727 = 6945242563 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(148, 295680983), (104, 489999817), (144, 611441850), (96, 928426832), (128, 770848297), (112, 880272723), (128, 978841016), (100, 1072708005), (64, 917023040)]) (.cons c245727_0 (.cons c245727_1 (.cons c245727_2 (.cons c245727_3 (.cons c245727_4 (.cons c245727_5 (.cons c245727_6 (.cons c245727_7 (.cons c245727_8 (.nil)))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(245725, 360), (245727, 360)]

theorem segOK : checkSeg 20 perms 245725 245738 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 245725 245738 720 4010590359360 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 4010590359360)
    (SegSum.cons (w := 360) h245725 (SegSum.cons (w := 360) h245727 (show SegSum (P.leaf 36) [] 0 from rfl))) (by decide)

end RACert.S6N0.C0.S135
