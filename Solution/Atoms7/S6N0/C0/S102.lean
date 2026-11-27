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

namespace RACert.S6N0.C0.S102

open RACert RACert.Problem

theorem cover241663 : P.CoversSplit 26 10 241663 0xffffffffffffffffffffffffffffaaaaffffffffffffffccffffaaaaffccaa88ffffffffffffffffffffaaaaffffaaaaffffffffffffffccffffaaaaffccaa88ffffffffffffffffffffffffffffaaaaffffffffffccffccffffaaaaffccaa88ffffffffffffffffffffaaaaffffaaaaffffffffffccffccffffaaaaffccaa88 :=
  coversSplit check rows (by decide) (by decide) (xs := [881, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f241663 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (247462912 + i)

theorem c241663_0 : rowSum f241663 0 178 = 789056631 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 241663) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover241663 (by decide)
  decide +kernel

theorem c241663_1 : rowSum f241663 178 186 = 1274436676 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 241663) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover241663 (by decide)
  decide +kernel

theorem c241663_2 : rowSum f241663 364 198 = 1899514975 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 241663) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover241663 (by decide)
  decide +kernel

theorem c241663_3 : rowSum f241663 562 200 = 1732189556 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 241663) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover241663 (by decide)
  decide +kernel

theorem c241663_4 : rowSum f241663 762 166 = 2232098252 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 241663) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover241663 (by decide)
  decide +kernel

theorem c241663_5 : rowSum f241663 928 96 = 1180638298 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 241663) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover241663 (by decide)
  decide +kernel

theorem sum241663 : rowSum f241663 0 1024 = 9107934388 :=
  rowSum_append (F := f241663) (lo := 0) (n := 178) (m := 846) (A := 789056631) (B := 8318877757) c241663_0 (rowSum_append (F := f241663) (lo := 178) (n := 186) (m := 660) (A := 1274436676) (B := 7044441081) c241663_1 (rowSum_append (F := f241663) (lo := 364) (n := 198) (m := 462) (A := 1899514975) (B := 5144926106) c241663_2 (rowSum_append (F := f241663) (lo := 562) (n := 200) (m := 262) (A := 1732189556) (B := 3412736550) c241663_3 (rowSum_append (F := f241663) (lo := 762) (n := 166) (m := 96) (A := 2232098252) (B := 1180638298) c241663_4 (c241663_5)))))

theorem h241663 : P.leaf 36 241663 = 9107934388 :=
  leaf_weighted (k := 26) (d := 10) (H := 241663) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 241663) (by decide) (by decide +kernel)) sum241663

theorem cover242467 : P.CoversSplit 26 10 242467 0xfffffffffffffffffffffafafffff0f0ffffffffffccccccffffaaaaff008000fffffafafffffafafafaa0a0fafaa0a0fffffafaffccc8c8fafaa0a0fa008000ffffffffffccffccfffffafaffccf0c0ffccffcccc00cc00ffccaa88cc0080000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 538, 579, 873, 930, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f242467 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 26 (248286208 + i)

theorem c242467_0 : rowSum f242467 0 443 = 59990548 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 242467) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover242467 (by decide)
  decide +kernel

theorem c242467_1 : rowSum f242467 443 411 = 107579628 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 242467) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover242467 (by decide)
  decide +kernel

theorem c242467_2 : rowSum f242467 854 170 = 86774280 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 242467) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover242467 (by decide)
  decide +kernel

theorem sum242467 : rowSum f242467 0 1024 = 254344456 :=
  rowSum_append (F := f242467) (lo := 0) (n := 443) (m := 581) (A := 59990548) (B := 194353908) c242467_0 (rowSum_append (F := f242467) (lo := 443) (n := 411) (m := 170) (A := 107579628) (B := 86774280) c242467_1 (c242467_2))

theorem h242467 : P.leaf 36 242467 = 254344456 :=
  leaf_weighted (k := 26) (d := 10) (H := 242467) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 242467) (by decide) (by decide +kernel)) sum242467

theorem cover242471 : P.CoversSplit 26 10 242471 0xfffffffffffffffffffffffffffff0f0ffffffffffffccccffffaaaaff008000fffffafafffffafafafaa0a0fafaa0a0fffffafaffffc8c8fafaa0a0fa008000ffffffffffccffccffffffffffccf0c0ffccffcccc00cc00ffccaa88cc0080000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 579, 873, 930, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f242471 (i : ℕ) := rowWeight keep9 twice9 i * P.leaf 26 (248290304 + i)

theorem c242471_0 : rowSum f242471 0 559 = 126905787 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 242471) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover242471 (by decide)
  decide +kernel

theorem c242471_1 : rowSum f242471 559 260 = 112871690 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 242471) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover242471 (by decide)
  decide +kernel

theorem c242471_2 : rowSum f242471 819 205 = 156828885 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 242471) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover242471 (by decide)
  decide +kernel

theorem sum242471 : rowSum f242471 0 1024 = 396606362 :=
  rowSum_append (F := f242471) (lo := 0) (n := 559) (m := 465) (A := 126905787) (B := 269700575) c242471_0 (rowSum_append (F := f242471) (lo := 559) (n := 260) (m := 205) (A := 112871690) (B := 156828885) c242471_1 (c242471_2))

theorem h242471 : P.leaf 36 242471 = 396606362 :=
  leaf_weighted (k := 26) (d := 10) (H := 242471) (keep := keep9) (twice := twice9) rows (by decide) (by decide) bal9 (invRow9 (H := 242471) (by decide) (by decide +kernel)) sum242471

theorem cover242479 : P.CoversSplit 26 10 242479 0xfffffffffffffffffffffffffffff0f0ffffffffffffccccffffaaaaff008000fffffafafffffafafafaa0a0fafaa0a0fffffafaffffc8c8fafaa0a0fa008000ffffffffffccffccffffffffffccf0c0ffccffcccc00cc00ffccaa88cc0080000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 579, 873, 930, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f242479 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 26 (248298496 + i)

theorem c242479_0 : rowSum f242479 0 439 = 161980866 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 242479) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover242479 (by decide)
  decide +kernel

theorem c242479_1 : rowSum f242479 439 391 = 277411754 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 242479) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover242479 (by decide)
  decide +kernel

theorem c242479_2 : rowSum f242479 830 194 = 241358162 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 242479) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover242479 (by decide)
  decide +kernel

theorem sum242479 : rowSum f242479 0 1024 = 680750782 :=
  rowSum_append (F := f242479) (lo := 0) (n := 439) (m := 585) (A := 161980866) (B := 518769916) c242479_0 (rowSum_append (F := f242479) (lo := 439) (n := 391) (m := 194) (A := 277411754) (B := 241358162) c242479_1 (c242479_2))

theorem h242479 : P.leaf 36 242479 = 680750782 :=
  leaf_weighted (k := 26) (d := 10) (H := 242479) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 242479) (by decide) (by decide +kernel)) sum242479

theorem cover242487 : P.CoversSplit 26 10 242487 0xfffffffffffffffffffffffffffff0f0ffffffffffffccccffffaaaaff008000fffffafafffffafaffffa0a0ffffa0a0fffffafaffffc8c8ffffa0a0ff008000fffffffffffffffffffffffffffff0f0ffccffcccc00cc00ffccaa88cc008000fffffafafffffafaffffa0a0ffffa0a0ffccfac8cc00c800ffcca080cc008000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 873, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c242487_0 : P.sumLeaves 26 248306688 204 = 21890839 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242487) (lo := 0) (len := 204) (W := 21890839) check rows elimOK (by decide) (by decide) cover242487 (by decide)
  decide +kernel

theorem c242487_1 : P.sumLeaves 26 248306892 173 = 74264236 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242487) (lo := 204) (len := 173) (W := 74264236) check rows elimOK (by decide) (by decide) cover242487 (by decide)
  decide +kernel

theorem c242487_2 : P.sumLeaves 26 248307065 104 = 91879749 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242487) (lo := 377) (len := 104) (W := 91879749) check rows elimOK (by decide) (by decide) cover242487 (by decide)
  decide +kernel

theorem c242487_3 : P.sumLeaves 26 248307169 145 = 116492730 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242487) (lo := 481) (len := 145) (W := 116492730) check rows elimOK (by decide) (by decide) cover242487 (by decide)
  decide +kernel

theorem c242487_4 : P.sumLeaves 26 248307314 128 = 87882727 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242487) (lo := 626) (len := 128) (W := 87882727) check rows elimOK (by decide) (by decide) cover242487 (by decide)
  decide +kernel

theorem c242487_5 : P.sumLeaves 26 248307442 135 = 126068331 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242487) (lo := 754) (len := 135) (W := 126068331) check rows elimOK (by decide) (by decide) cover242487 (by decide)
  decide +kernel

theorem c242487_6 : P.sumLeaves 26 248307577 104 = 115403698 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242487) (lo := 889) (len := 104) (W := 115403698) check rows elimOK (by decide) (by decide) cover242487 (by decide)
  decide +kernel

theorem c242487_7 : P.sumLeaves 26 248307681 31 = 85770132 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242487) (lo := 993) (len := 31) (W := 85770132) check rows elimOK (by decide) (by decide) cover242487 (by decide)
  decide +kernel

theorem h242487 : P.leaf 36 242487 = 719652442 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(204, 21890839), (173, 74264236), (104, 91879749), (145, 116492730), (128, 87882727), (135, 126068331), (104, 115403698), (31, 85770132)]) (.cons c242487_0 (.cons c242487_1 (.cons c242487_2 (.cons c242487_3 (.cons c242487_4 (.cons c242487_5 (.cons c242487_6 (.cons c242487_7 (.nil))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(241663, 90), (242467, 12), (242471, 120), (242479, 180), (242487, 360)]

theorem segOK : checkSeg 20 perms 241663 242495 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 241663 242495 762 1251969011712 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1251969011712)
    (SegSum.cons (w := 90) h241663 (SegSum.cons (w := 12) h242467 (SegSum.cons (w := 120) h242471 (SegSum.cons (w := 180) h242479 (SegSum.cons (w := 360) h242487 (show SegSum (P.leaf 36) [] 0 from rfl)))))) (by decide)

end RACert.S6N0.C0.S102
