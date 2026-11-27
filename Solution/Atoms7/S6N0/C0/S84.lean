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

namespace RACert.S6N0.C0.S84

open RACert RACert.Problem

theorem cover120823 : P.CoversSplit 26 10 120823 0xfffffffffffffafafffffffffffffafaffffffffffffc8c8fafafafac8c8c8c8fffffafafffffafafafafafafafafafafffffafaffffc8c8fafafafac8c8c8c8fffffffffffffafafffffffffffffafaffffffffccccc8c8fafafafac8c8c8c8fffffafafffffafafafafafafafafafafffffafaccccc8c8fafafafac8c8c8c8 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 873, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f120823 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (123722752 + i)

theorem c120823_0 : rowSum f120823 0 240 = 213087430 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 120823) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover120823 (by decide)
  decide +kernel

theorem c120823_1 : rowSum f120823 240 180 = 505477488 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 120823) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover120823 (by decide)
  decide +kernel

theorem c120823_2 : rowSum f120823 420 189 = 602643464 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 120823) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover120823 (by decide)
  decide +kernel

theorem c120823_3 : rowSum f120823 609 213 = 724052571 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 120823) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover120823 (by decide)
  decide +kernel

theorem c120823_4 : rowSum f120823 822 194 = 892237206 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 120823) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover120823 (by decide)
  decide +kernel

theorem c120823_5 : rowSum f120823 1016 8 = 103650334 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 120823) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover120823 (by decide)
  decide +kernel

theorem sum120823 : rowSum f120823 0 1024 = 3041148493 :=
  rowSum_append (F := f120823) (lo := 0) (n := 240) (m := 784) (A := 213087430) (B := 2828061063) c120823_0 (rowSum_append (F := f120823) (lo := 240) (n := 180) (m := 604) (A := 505477488) (B := 2322583575) c120823_1 (rowSum_append (F := f120823) (lo := 420) (n := 189) (m := 415) (A := 602643464) (B := 1719940111) c120823_2 (rowSum_append (F := f120823) (lo := 609) (n := 213) (m := 202) (A := 724052571) (B := 995887540) c120823_3 (rowSum_append (F := f120823) (lo := 822) (n := 194) (m := 8) (A := 892237206) (B := 103650334) c120823_4 (c120823_5)))))

theorem h120823 : P.leaf 36 120823 = 3041148493 :=
  leaf_weighted (k := 26) (d := 10) (H := 120823) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 120823) (by decide) (by decide +kernel)) sum120823

theorem cover120827 : P.CoversSplit 26 10 120827 0xf0f00000f0f000000000000000000000f0f00000f0f000000000000000000000f0f00000f0f000000000505000005050f0f00000f0f000000000505000004040f0f00000f0f000000000000000000000f0f00000c0c000000000000000000000f0f00000f0f000000000505000005050f0f00000c0c000000000505000004040 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 873, 922, 1273, 1322]) (by decide +kernel)

noncomputable def f120827 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (123726848 + i)

theorem c120827_0 : rowSum f120827 0 892 = 475026127 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 120827) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover120827 (by decide)
  decide +kernel

theorem c120827_1 : rowSum f120827 892 132 = 171875212 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 120827) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover120827 (by decide)
  decide +kernel

theorem sum120827 : rowSum f120827 0 1024 = 646901339 :=
  rowSum_append (F := f120827) (lo := 0) (n := 892) (m := 132) (A := 475026127) (B := 171875212) c120827_0 (c120827_1)

theorem h120827 : P.leaf 36 120827 = 646901339 :=
  leaf_weighted (k := 26) (d := 10) (H := 120827) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 120827) (by decide) (by decide +kernel)) sum120827

theorem cover120828 : P.CoversSplit 26 10 120828 0xfffffffffffffafafffffffffffffafaffffffffffffc8c8fafafafac8c8c8c8fffffafafffffafafafaf0f0fafaf0f0fffffafaffffc8c8fafaf0f0c8c8c0c0fffffffffffffafafffffffffffffafaffffffffccccc8c8fafafafac8c8c8c8fffffafafffffafafafaf0f0fafaf0f0fffffafaccccc8c8fafaf0f0c8c8c0c0 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f120828 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (123727872 + i)

theorem c120828_0 : rowSum f120828 0 250 = 35901840 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 120828) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover120828 (by decide)
  decide +kernel

theorem c120828_1 : rowSum f120828 250 180 = 90189746 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 120828) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover120828 (by decide)
  decide +kernel

theorem c120828_2 : rowSum f120828 430 198 = 165190053 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 120828) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover120828 (by decide)
  decide +kernel

theorem c120828_3 : rowSum f120828 628 232 = 302846349 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 120828) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover120828 (by decide)
  decide +kernel

theorem c120828_4 : rowSum f120828 860 164 = 408164909 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 120828) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover120828 (by decide)
  decide +kernel

theorem sum120828 : rowSum f120828 0 1024 = 1002292897 :=
  rowSum_append (F := f120828) (lo := 0) (n := 250) (m := 774) (A := 35901840) (B := 966391057) c120828_0 (rowSum_append (F := f120828) (lo := 250) (n := 180) (m := 594) (A := 90189746) (B := 876201311) c120828_1 (rowSum_append (F := f120828) (lo := 430) (n := 198) (m := 396) (A := 165190053) (B := 711011258) c120828_2 (rowSum_append (F := f120828) (lo := 628) (n := 232) (m := 164) (A := 302846349) (B := 408164909) c120828_3 (c120828_4))))

theorem h120828 : P.leaf 36 120828 = 1002292897 :=
  leaf_weighted (k := 26) (d := 10) (H := 120828) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 120828) (by decide) (by decide +kernel)) sum120828

theorem cover120829 : P.CoversSplit 26 10 120829 0xfffffffffffffafafffffffffffffafaffffffffffffc8c8fafafafac8c8c8c8fffffafafffffafafafaf0f0fafaf0f0fffffafaffffc8c8fafaf0f0c8c8c0c0fffffffffffffafafffffffffffffafaffffffffccccc8c8fafafafac8c8c8c8fffffafafffffafafafaf0f0fafaf0f0fffffafaccccc8c8fafaf0f0c8c8c0c0 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 922, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c120829_0 : P.sumLeaves 26 123728896 172 = 110508156 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120829) (lo := 0) (len := 172) (W := 110508156) check rows elimOK (by decide) (by decide) cover120829 (by decide)
  decide +kernel

theorem c120829_1 : P.sumLeaves 26 123729068 133 = 137121143 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120829) (lo := 172) (len := 133) (W := 137121143) check rows elimOK (by decide) (by decide) cover120829 (by decide)
  decide +kernel

theorem c120829_2 : P.sumLeaves 26 123729201 121 = 197908173 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120829) (lo := 305) (len := 121) (W := 197908173) check rows elimOK (by decide) (by decide) cover120829 (by decide)
  decide +kernel

theorem c120829_3 : P.sumLeaves 26 123729322 130 = 333519382 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120829) (lo := 426) (len := 130) (W := 333519382) check rows elimOK (by decide) (by decide) cover120829 (by decide)
  decide +kernel

theorem c120829_4 : P.sumLeaves 26 123729452 136 = 287431618 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120829) (lo := 556) (len := 136) (W := 287431618) check rows elimOK (by decide) (by decide) cover120829 (by decide)
  decide +kernel

theorem c120829_5 : P.sumLeaves 26 123729588 133 = 534768772 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120829) (lo := 692) (len := 133) (W := 534768772) check rows elimOK (by decide) (by decide) cover120829 (by decide)
  decide +kernel

theorem c120829_6 : P.sumLeaves 26 123729721 111 = 348930606 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120829) (lo := 825) (len := 111) (W := 348930606) check rows elimOK (by decide) (by decide) cover120829 (by decide)
  decide +kernel

theorem c120829_7 : P.sumLeaves 26 123729832 88 = 666811838 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120829) (lo := 936) (len := 88) (W := 666811838) check rows elimOK (by decide) (by decide) cover120829 (by decide)
  decide +kernel

theorem h120829 : P.leaf 36 120829 = 2616999688 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(172, 110508156), (133, 137121143), (121, 197908173), (130, 333519382), (136, 287431618), (133, 534768772), (111, 348930606), (88, 666811838)]) (.cons c120829_0 (.cons c120829_1 (.cons c120829_2 (.cons c120829_3 (.cons c120829_4 (.cons c120829_5 (.cons c120829_6 (.cons c120829_7 (.nil))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(120823, 360), (120827, 360), (120828, 360), (120829, 720)]

theorem segOK : checkSeg 20 perms 120823 120831 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 120823 120831 1800 3572763157800 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 3572763157800)
    (SegSum.cons (w := 360) h120823 (SegSum.cons (w := 360) h120827 (SegSum.cons (w := 360) h120828 (SegSum.cons (w := 720) h120829 (show SegSum (P.leaf 36) [] 0 from rfl))))) (by decide)

end RACert.S6N0.C0.S84
