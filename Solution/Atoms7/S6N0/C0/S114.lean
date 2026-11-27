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

namespace RACert.S6N0.C0.S114

open RACert RACert.Problem

theorem cover241501 : P.CoversSplit 26 10 241501 0xffffffffffffffffffffffffffffaaaaffffffffffffff00ffffaaaaff00aa00ffffffffffffffffffffaaaaffffaaaaffffffffffffff00ffffaaaaff00aa00ffffffffffffffffffffffffffffaaaaffffffffff00ff00ffffaaaaff00aa00ffffffffffffffffffffaaaaffffaaaaffffffffff00ff00ffffaaaaff00aa00 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 579, 881, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c241501_0 : P.sumLeaves 26 247297024 148 = 16165330 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241501) (lo := 0) (len := 148) (W := 16165330) check rows elimOK (by decide) (by decide) cover241501 (by decide)
  decide +kernel

theorem c241501_1 : P.sumLeaves 26 247297172 104 = 29391930 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241501) (lo := 148) (len := 104) (W := 29391930) check rows elimOK (by decide) (by decide) cover241501 (by decide)
  decide +kernel

theorem c241501_2 : P.sumLeaves 26 247297276 148 = 51691288 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241501) (lo := 252) (len := 148) (W := 51691288) check rows elimOK (by decide) (by decide) cover241501 (by decide)
  decide +kernel

theorem c241501_3 : P.sumLeaves 26 247297424 96 = 75167063 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241501) (lo := 400) (len := 96) (W := 75167063) check rows elimOK (by decide) (by decide) cover241501 (by decide)
  decide +kernel

theorem c241501_4 : P.sumLeaves 26 247297520 132 = 72715417 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241501) (lo := 496) (len := 132) (W := 72715417) check rows elimOK (by decide) (by decide) cover241501 (by decide)
  decide +kernel

theorem c241501_5 : P.sumLeaves 26 247297652 112 = 76285950 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241501) (lo := 628) (len := 112) (W := 76285950) check rows elimOK (by decide) (by decide) cover241501 (by decide)
  decide +kernel

theorem c241501_6 : P.sumLeaves 26 247297764 132 = 106289304 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241501) (lo := 740) (len := 132) (W := 106289304) check rows elimOK (by decide) (by decide) cover241501 (by decide)
  decide +kernel

theorem c241501_7 : P.sumLeaves 26 247297896 104 = 128830064 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241501) (lo := 872) (len := 104) (W := 128830064) check rows elimOK (by decide) (by decide) cover241501 (by decide)
  decide +kernel

theorem c241501_8 : P.sumLeaves 26 247298000 48 = 135330144 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241501) (lo := 976) (len := 48) (W := 135330144) check rows elimOK (by decide) (by decide) cover241501 (by decide)
  decide +kernel

theorem h241501 : P.leaf 36 241501 = 691866490 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(148, 16165330), (104, 29391930), (148, 51691288), (96, 75167063), (132, 72715417), (112, 76285950), (132, 106289304), (104, 128830064), (48, 135330144)]) (.cons c241501_0 (.cons c241501_1 (.cons c241501_2 (.cons c241501_3 (.cons c241501_4 (.cons c241501_5 (.cons c241501_6 (.cons c241501_7 (.cons c241501_8 (.nil)))))))))) (by decide) (by decide))

theorem cover241503 : P.CoversSplit 26 10 241503 0xffffffffffffffffffffffffffffaaaaffffffffffffff00ffffaaaaff00aa00ffffffffffffffffffffaaaaffffaaaaffffffffffffff00ffffaaaaff00aa00ffffffffffffffffffffffffffffaaaaffffffffff00ff00ffffaaaaff00aa00ffffffffffffffffffffaaaaffffaaaaffffffffff00ff00ffffaaaaff00aa00 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 881, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c241503_0 : P.sumLeaves 26 247299072 148 = 62749108 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241503) (lo := 0) (len := 148) (W := 62749108) check rows elimOK (by decide) (by decide) cover241503 (by decide)
  decide +kernel

theorem c241503_1 : P.sumLeaves 26 247299220 104 = 118185594 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241503) (lo := 148) (len := 104) (W := 118185594) check rows elimOK (by decide) (by decide) cover241503 (by decide)
  decide +kernel

theorem c241503_2 : P.sumLeaves 26 247299324 148 = 168192657 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241503) (lo := 252) (len := 148) (W := 168192657) check rows elimOK (by decide) (by decide) cover241503 (by decide)
  decide +kernel

theorem c241503_3 : P.sumLeaves 26 247299472 96 = 238490234 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241503) (lo := 400) (len := 96) (W := 238490234) check rows elimOK (by decide) (by decide) cover241503 (by decide)
  decide +kernel

theorem c241503_4 : P.sumLeaves 26 247299568 132 = 230240797 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241503) (lo := 496) (len := 132) (W := 230240797) check rows elimOK (by decide) (by decide) cover241503 (by decide)
  decide +kernel

theorem c241503_5 : P.sumLeaves 26 247299700 112 = 227875968 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241503) (lo := 628) (len := 112) (W := 227875968) check rows elimOK (by decide) (by decide) cover241503 (by decide)
  decide +kernel

theorem c241503_6 : P.sumLeaves 26 247299812 132 = 294563636 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241503) (lo := 740) (len := 132) (W := 294563636) check rows elimOK (by decide) (by decide) cover241503 (by decide)
  decide +kernel

theorem c241503_7 : P.sumLeaves 26 247299944 104 = 288010142 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241503) (lo := 872) (len := 104) (W := 288010142) check rows elimOK (by decide) (by decide) cover241503 (by decide)
  decide +kernel

theorem c241503_8 : P.sumLeaves 26 247300048 48 = 279070192 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241503) (lo := 976) (len := 48) (W := 279070192) check rows elimOK (by decide) (by decide) cover241503 (by decide)
  decide +kernel

theorem h241503 : P.leaf 36 241503 = 1907378328 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(148, 62749108), (104, 118185594), (148, 168192657), (96, 238490234), (132, 230240797), (112, 227875968), (132, 294563636), (104, 288010142), (48, 279070192)]) (.cons c241503_0 (.cons c241503_1 (.cons c241503_2 (.cons c241503_3 (.cons c241503_4 (.cons c241503_5 (.cons c241503_6 (.cons c241503_7 (.cons c241503_8 (.nil)))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(241501, 120), (241503, 180)]

theorem segOK : checkSeg 20 perms 241501 241514 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 241501 241514 300 426352077840 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 426352077840)
    (SegSum.cons (w := 120) h241501 (SegSum.cons (w := 180) h241503 (show SegSum (P.leaf 36) [] 0 from rfl))) (by decide)

end RACert.S6N0.C0.S114
