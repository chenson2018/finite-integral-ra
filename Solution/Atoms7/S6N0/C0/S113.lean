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

namespace RACert.S6N0.C0.S113

open RACert RACert.Problem

theorem cover245724 : P.CoversSplit 26 10 245724 0xfffffffffffffffffffffffffffffafaffffffffffffff00ffffaaaaffccaa00ffffffffffffffffffffaaaaffffaaaaffffffffffffff00ffffaaaaffccaa00fffffffffffffffffffffffffffffafaffffffffff00ff00ffffaaaaff00aa00ffffffffffffffffffffaaaaffffaaaaffffffffff00ff00ffffaaaaff00aa00 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f245724 (i : ℕ) := rowWeight keep10 twice10 i * P.leaf 26 (251621376 + i)

theorem c245724_0 : rowSum f245724 0 241 = 34021376 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 245724) (keep := keep10) (twice := twice10) check rows elimOK (by decide) (by decide) cover245724 (by decide)
  decide +kernel

theorem c245724_1 : rowSum f245724 241 148 = 168863756 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 245724) (keep := keep10) (twice := twice10) check rows elimOK (by decide) (by decide) cover245724 (by decide)
  decide +kernel

theorem c245724_2 : rowSum f245724 389 98 = 411309500 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 245724) (keep := keep10) (twice := twice10) check rows elimOK (by decide) (by decide) cover245724 (by decide)
  decide +kernel

theorem c245724_3 : rowSum f245724 487 399 = 514028372 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 245724) (keep := keep10) (twice := twice10) check rows elimOK (by decide) (by decide) cover245724 (by decide)
  decide +kernel

theorem c245724_4 : rowSum f245724 886 138 = 587357236 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 245724) (keep := keep10) (twice := twice10) check rows elimOK (by decide) (by decide) cover245724 (by decide)
  decide +kernel

theorem sum245724 : rowSum f245724 0 1024 = 1715580240 :=
  rowSum_append (F := f245724) (lo := 0) (n := 241) (m := 783) (A := 34021376) (B := 1681558864) c245724_0 (rowSum_append (F := f245724) (lo := 241) (n := 148) (m := 635) (A := 168863756) (B := 1512695108) c245724_1 (rowSum_append (F := f245724) (lo := 389) (n := 98) (m := 537) (A := 411309500) (B := 1101385608) c245724_2 (rowSum_append (F := f245724) (lo := 487) (n := 399) (m := 138) (A := 514028372) (B := 587357236) c245724_3 (c245724_4))))

theorem h245724 : P.leaf 36 245724 = 1715580240 :=
  leaf_weighted (k := 26) (d := 10) (H := 245724) (keep := keep10) (twice := twice10) rows (by decide) (by decide) bal10 (invRow10 (H := 245724) (by decide) (by decide +kernel)) sum245724

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

noncomputable def f245727 (i : ℕ) := rowWeight keep10 twice10 i * P.leaf 26 (251624448 + i)

theorem c245727_0 : rowSum f245727 0 241 = 706495376 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 245727) (keep := keep10) (twice := twice10) check rows elimOK (by decide) (by decide) cover245727 (by decide)
  decide +kernel

theorem c245727_1 : rowSum f245727 241 148 = 1196402092 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 245727) (keep := keep10) (twice := twice10) check rows elimOK (by decide) (by decide) cover245727 (by decide)
  decide +kernel

theorem c245727_2 : rowSum f245727 389 98 = 1819270112 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 245727) (keep := keep10) (twice := twice10) check rows elimOK (by decide) (by decide) cover245727 (by decide)
  decide +kernel

theorem c245727_3 : rowSum f245727 487 399 = 1947643675 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 245727) (keep := keep10) (twice := twice10) check rows elimOK (by decide) (by decide) cover245727 (by decide)
  decide +kernel

theorem c245727_4 : rowSum f245727 886 138 = 1275431308 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 245727) (keep := keep10) (twice := twice10) check rows elimOK (by decide) (by decide) cover245727 (by decide)
  decide +kernel

theorem sum245727 : rowSum f245727 0 1024 = 6945242563 :=
  rowSum_append (F := f245727) (lo := 0) (n := 241) (m := 783) (A := 706495376) (B := 6238747187) c245727_0 (rowSum_append (F := f245727) (lo := 241) (n := 148) (m := 635) (A := 1196402092) (B := 5042345095) c245727_1 (rowSum_append (F := f245727) (lo := 389) (n := 98) (m := 537) (A := 1819270112) (B := 3223074983) c245727_2 (rowSum_append (F := f245727) (lo := 487) (n := 399) (m := 138) (A := 1947643675) (B := 1275431308) c245727_3 (c245727_4))))

theorem h245727 : P.leaf 36 245727 = 6945242563 :=
  leaf_weighted (k := 26) (d := 10) (H := 245727) (keep := keep10) (twice := twice10) rows (by decide) (by decide) bal10 (invRow10 (H := 245727) (by decide) (by decide +kernel)) sum245727

def seg : List (ℕ × ℕ) := [(245724, 60), (245725, 360), (245727, 360)]

theorem segOK : checkSeg 20 perms 245724 245738 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 245724 245738 780 4113525173760 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 4113525173760)
    (SegSum.cons (w := 60) h245724 (SegSum.cons (w := 360) h245725 (SegSum.cons (w := 360) h245727 (show SegSum (P.leaf 36) [] 0 from rfl)))) (by decide)

end RACert.S6N0.C0.S113
