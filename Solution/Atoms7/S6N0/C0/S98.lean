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

namespace RACert.S6N0.C0.S98

open RACert RACert.Problem

theorem cover241500 : P.CoversSplit 26 10 241500 0xffffffffffffffffffffffffffffaaaaffffffffffffff00ffffaaaaff00aa00ffffffffffffffffffffaaaaffffaaaaffffffffffffff00ffffaaaaff00aa00ffffffffffffffffffffffffffffaaaaffffffffff00ff00ffffaaaaff00aa00ffffffffffffffffffffaaaaffffaaaaffffffffff00ff00ffffaaaaff00aa00 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 881, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f241500 (i : ℕ) := rowWeight keep8 twice8 i * P.leaf 26 (247296000 + i)

theorem c241500_0 : rowSum f241500 0 241 = 5655488 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 241500) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover241500 (by decide)
  decide +kernel

theorem c241500_1 : rowSum f241500 241 150 = 12363744 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 241500) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover241500 (by decide)
  decide +kernel

theorem c241500_2 : rowSum f241500 391 100 = 20618784 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 241500) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover241500 (by decide)
  decide +kernel

theorem c241500_3 : rowSum f241500 491 403 = 52802704 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 241500) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover241500 (by decide)
  decide +kernel

theorem c241500_4 : rowSum f241500 894 130 = 50618288 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 241500) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover241500 (by decide)
  decide +kernel

theorem sum241500 : rowSum f241500 0 1024 = 142059008 :=
  rowSum_append (F := f241500) (lo := 0) (n := 241) (m := 783) (A := 5655488) (B := 136403520) c241500_0 (rowSum_append (F := f241500) (lo := 241) (n := 150) (m := 633) (A := 12363744) (B := 124039776) c241500_1 (rowSum_append (F := f241500) (lo := 391) (n := 100) (m := 533) (A := 20618784) (B := 103420992) c241500_2 (rowSum_append (F := f241500) (lo := 491) (n := 403) (m := 130) (A := 52802704) (B := 50618288) c241500_3 (c241500_4))))

theorem h241500 : P.leaf 36 241500 = 142059008 :=
  leaf_weighted (k := 26) (d := 10) (H := 241500) (keep := keep8) (twice := twice8) rows (by decide) (by decide) bal8 (invRow8 (H := 241500) (by decide) (by decide +kernel)) sum241500

theorem cover241501 : P.CoversSplit 26 10 241501 0xffffffffffffffffffffffffffffaaaaffffffffffffff00ffffaaaaff00aa00ffffffffffffffffffffaaaaffffaaaaffffffffffffff00ffffaaaaff00aa00ffffffffffffffffffffffffffffaaaaffffffffff00ff00ffffaaaaff00aa00ffffffffffffffffffffaaaaffffaaaaffffffffff00ff00ffffaaaaff00aa00 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 579, 881, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f241501 (i : ℕ) := rowWeight keep8 twice8 i * P.leaf 26 (247297024 + i)

theorem c241501_0 : rowSum f241501 0 241 = 38166092 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 241501) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover241501 (by decide)
  decide +kernel

theorem c241501_1 : rowSum f241501 241 150 = 102793520 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 241501) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover241501 (by decide)
  decide +kernel

theorem c241501_2 : rowSum f241501 391 100 = 137374414 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 241501) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover241501 (by decide)
  decide +kernel

theorem c241501_3 : rowSum f241501 491 403 = 250442960 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 241501) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover241501 (by decide)
  decide +kernel

theorem c241501_4 : rowSum f241501 894 130 = 163089504 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 241501) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover241501 (by decide)
  decide +kernel

theorem sum241501 : rowSum f241501 0 1024 = 691866490 :=
  rowSum_append (F := f241501) (lo := 0) (n := 241) (m := 783) (A := 38166092) (B := 653700398) c241501_0 (rowSum_append (F := f241501) (lo := 241) (n := 150) (m := 633) (A := 102793520) (B := 550906878) c241501_1 (rowSum_append (F := f241501) (lo := 391) (n := 100) (m := 533) (A := 137374414) (B := 413532464) c241501_2 (rowSum_append (F := f241501) (lo := 491) (n := 403) (m := 130) (A := 250442960) (B := 163089504) c241501_3 (c241501_4))))

theorem h241501 : P.leaf 36 241501 = 691866490 :=
  leaf_weighted (k := 26) (d := 10) (H := 241501) (keep := keep8) (twice := twice8) rows (by decide) (by decide) bal8 (invRow8 (H := 241501) (by decide) (by decide +kernel)) sum241501

theorem cover241503 : P.CoversSplit 26 10 241503 0xffffffffffffffffffffffffffffaaaaffffffffffffff00ffffaaaaff00aa00ffffffffffffffffffffaaaaffffaaaaffffffffffffff00ffffaaaaff00aa00ffffffffffffffffffffffffffffaaaaffffffffff00ff00ffffaaaaff00aa00ffffffffffffffffffffaaaaffffaaaaffffffffff00ff00ffffaaaaff00aa00 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 881, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f241503 (i : ℕ) := rowWeight keep8 twice8 i * P.leaf 26 (247299072 + i)

theorem c241503_0 : rowSum f241503 0 241 = 152164446 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 241503) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover241503 (by decide)
  decide +kernel

theorem c241503_1 : rowSum f241503 241 150 = 332001274 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 241503) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover241503 (by decide)
  decide +kernel

theorem c241503_2 : rowSum f241503 391 100 = 449224260 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 241503) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover241503 (by decide)
  decide +kernel

theorem c241503_3 : rowSum f241503 491 403 = 635482652 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 241503) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover241503 (by decide)
  decide +kernel

theorem c241503_4 : rowSum f241503 894 130 = 338505696 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 241503) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover241503 (by decide)
  decide +kernel

theorem sum241503 : rowSum f241503 0 1024 = 1907378328 :=
  rowSum_append (F := f241503) (lo := 0) (n := 241) (m := 783) (A := 152164446) (B := 1755213882) c241503_0 (rowSum_append (F := f241503) (lo := 241) (n := 150) (m := 633) (A := 332001274) (B := 1423212608) c241503_1 (rowSum_append (F := f241503) (lo := 391) (n := 100) (m := 533) (A := 449224260) (B := 973988348) c241503_2 (rowSum_append (F := f241503) (lo := 491) (n := 403) (m := 130) (A := 635482652) (B := 338505696) c241503_3 (c241503_4))))

theorem h241503 : P.leaf 36 241503 = 1907378328 :=
  leaf_weighted (k := 26) (d := 10) (H := 241503) (keep := keep8) (twice := twice8) rows (by decide) (by decide) bal8 (invRow8 (H := 241503) (by decide) (by decide +kernel)) sum241503

theorem cover241514 : P.CoversSplit 26 10 241514 0xffffffffffffffffffffffffffffaaaaffffffffffffffccffffaaaaff00aa00fffffffffffffffffafaaaaafafaaaaaffffffffffffffccfafaaaaafa00aa00ffffffffffffffffffffffffffffaaaaffffffffff00ff00ffffaaaaff00aa00fffffffffffffffffafaaaaafafaaaaaffffffffff00ff00fafaaaaafa00aa00 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 881, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c241514_0 : P.sumLeaves 26 247310336 158 = 4777446 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241514) (lo := 0) (len := 158) (W := 4777446) check rows elimOK (by decide) (by decide) cover241514 (by decide)
  decide +kernel

theorem c241514_1 : P.sumLeaves 26 247310494 128 = 10094971 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241514) (lo := 158) (len := 128) (W := 10094971) check rows elimOK (by decide) (by decide) cover241514 (by decide)
  decide +kernel

theorem c241514_2 : P.sumLeaves 26 247310622 128 = 31062432 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241514) (lo := 286) (len := 128) (W := 31062432) check rows elimOK (by decide) (by decide) cover241514 (by decide)
  decide +kernel

theorem c241514_3 : P.sumLeaves 26 247310750 96 = 78695742 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241514) (lo := 414) (len := 96) (W := 78695742) check rows elimOK (by decide) (by decide) cover241514 (by decide)
  decide +kernel

theorem c241514_4 : P.sumLeaves 26 247310846 139 = 41367684 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241514) (lo := 510) (len := 139) (W := 41367684) check rows elimOK (by decide) (by decide) cover241514 (by decide)
  decide +kernel

theorem c241514_5 : P.sumLeaves 26 247310985 115 = 57514024 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241514) (lo := 649) (len := 115) (W := 57514024) check rows elimOK (by decide) (by decide) cover241514 (by decide)
  decide +kernel

theorem c241514_6 : P.sumLeaves 26 247311100 128 = 67149135 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241514) (lo := 764) (len := 128) (W := 67149135) check rows elimOK (by decide) (by decide) cover241514 (by decide)
  decide +kernel

theorem c241514_7 : P.sumLeaves 26 247311228 104 = 80315254 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241514) (lo := 892) (len := 104) (W := 80315254) check rows elimOK (by decide) (by decide) cover241514 (by decide)
  decide +kernel

theorem c241514_8 : P.sumLeaves 26 247311332 28 = 79845084 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241514) (lo := 996) (len := 28) (W := 79845084) check rows elimOK (by decide) (by decide) cover241514 (by decide)
  decide +kernel

theorem h241514 : P.leaf 36 241514 = 450821772 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(158, 4777446), (128, 10094971), (128, 31062432), (96, 78695742), (139, 41367684), (115, 57514024), (128, 67149135), (104, 80315254), (28, 79845084)]) (.cons c241514_0 (.cons c241514_1 (.cons c241514_2 (.cons c241514_3 (.cons c241514_4 (.cons c241514_5 (.cons c241514_6 (.cons c241514_7 (.cons c241514_8 (.nil)))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(241500, 15), (241501, 120), (241503, 180), (241514, 90)]

theorem segOK : checkSeg 20 perms 241500 241515 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 241500 241515 405 469056922440 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 469056922440)
    (SegSum.cons (w := 15) h241500 (SegSum.cons (w := 120) h241501 (SegSum.cons (w := 180) h241503 (SegSum.cons (w := 90) h241514 (show SegSum (P.leaf 36) [] 0 from rfl))))) (by decide)

end RACert.S6N0.C0.S98
