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

theorem cover827295 : P.CoversSplit 26 10 827295 0xfffffffffffffffffffffafa00000000ffff0000ffcc0000ffff000000000000fffffffffffffffffffffafa00000000ffff0000ffcc0000ffff000000000000fffffffffffffffffffffafa00000000ffff0000ffcc0000ffff000000000000fffffffffffffffffffffafa00000000ffff0000ffcc0000ffff000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 1266, 1272]) (by decide +kernel)

noncomputable def f827295 (i : ℕ) := rowWeight keep10 twice10 i * P.leaf 26 (847150080 + i)

theorem c827295_0 : rowSum f827295 0 350 = 505970654 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 827295) (keep := keep10) (twice := twice10) check rows elimOK (by decide) (by decide) cover827295 (by decide)
  decide +kernel

theorem c827295_1 : rowSum f827295 350 148 = 668432176 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 827295) (keep := keep10) (twice := twice10) check rows elimOK (by decide) (by decide) cover827295 (by decide)
  decide +kernel

theorem c827295_2 : rowSum f827295 498 526 = 732975498 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 827295) (keep := keep10) (twice := twice10) check rows elimOK (by decide) (by decide) cover827295 (by decide)
  decide +kernel

theorem sum827295 : rowSum f827295 0 1024 = 1907378328 :=
  rowSum_append (F := f827295) (lo := 0) (n := 350) (m := 674) (A := 505970654) (B := 1401407674) c827295_0 (rowSum_append (F := f827295) (lo := 350) (n := 148) (m := 526) (A := 668432176) (B := 732975498) c827295_1 (c827295_2))

theorem h827295 : P.leaf 36 827295 = 1907378328 :=
  leaf_weighted (k := 26) (d := 10) (H := 827295) (keep := keep10) (twice := twice10) rows (by decide) (by decide) (bal10) (invRow10 (H := 827295) (by decide) (by decide +kernel)) sum827295

theorem h241503 : P.leaf 36 241503 = 1907378328 :=
  orient80 (v := 827295) (by decide) (by decide +kernel) h827295

theorem cover383891 : P.CoversSplit 26 10 383891 0xfcfcfcfca8a8a8a8fcfcf8f8a8a8a8a8fcfcfcfca888a888f8f8f8f888888888fcfcfcfca8a8a8a8f8f8f8f8a8a8a8a8fcfcfcfca888a888f8f8f8f888888888fcfcfcfca8a8a8a8fcfcf8f8a8a8a8a8fcfcfcfc88888888f8f8f8f888888888fcfcfcfca8a8a8a8f8f8f8f8a8a8a8a8fcfcfcfc88888888f8f8f8f888888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 482, 489, 537, 922, 1273, 1658, 1665]) (by decide +kernel)

noncomputable def f383891 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (393104384 + i)

theorem c383891_0 : rowSum f383891 0 318 = 55593318 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 383891) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover383891 (by decide)
  decide +kernel

theorem c383891_1 : rowSum f383891 318 184 = 181344580 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 383891) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover383891 (by decide)
  decide +kernel

theorem c383891_2 : rowSum f383891 502 522 = 213883874 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 383891) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover383891 (by decide)
  decide +kernel

theorem sum383891 : rowSum f383891 0 1024 = 450821772 :=
  rowSum_append (F := f383891) (lo := 0) (n := 318) (m := 706) (A := 55593318) (B := 395228454) c383891_0 (rowSum_append (F := f383891) (lo := 318) (n := 184) (m := 522) (A := 181344580) (B := 213883874) c383891_1 (c383891_2))

theorem h383891 : P.leaf 36 383891 = 450821772 :=
  leaf_weighted (k := 26) (d := 10) (H := 383891) (keep := keep4) (twice := twice4) rows (by decide) (by decide) (bal4) (invRow4 (H := 383891) (by decide) (by decide +kernel)) sum383891

theorem h241514 : P.leaf 36 241514 = 450821772 :=
  orient74 (v := 383891) (by decide) (by decide +kernel) h383891

theorem cover383447 : P.CoversSplit 26 10 383447 0xffffffffffffffffffffeeeeffffeeeeffeeffeeffeeffeefaeaeaeac8c8c8c8fffffffffffffffffafaaaaafafaaaaaffeeffeeffeeffeefaeaaaaac8c88888ffffffffffffffffffffeeeeffffeeeeffccffccccccccccfac8eac8c8c8c8c8fffffffffffffffffafaaaaafafaaaaaffccffccccccccccfac8aa88c8c88888 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 629, 636, 922, 1273, 1658, 1665]) (by decide +kernel)

noncomputable def f383447 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (392649728 + i)

theorem c383447_0 : rowSum f383447 0 271 = 95181996 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 383447) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover383447 (by decide)
  decide +kernel

theorem c383447_1 : rowSum f383447 271 151 = 240286166 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 383447) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover383447 (by decide)
  decide +kernel

theorem c383447_2 : rowSum f383447 422 373 = 380065976 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 383447) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover383447 (by decide)
  decide +kernel

theorem c383447_3 : rowSum f383447 795 209 = 547497138 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 383447) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover383447 (by decide)
  decide +kernel

theorem c383447_4 : rowSum f383447 1004 20 = 66658376 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 383447) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover383447 (by decide)
  decide +kernel

theorem sum383447 : rowSum f383447 0 1024 = 1329689652 :=
  rowSum_append (F := f383447) (lo := 0) (n := 271) (m := 753) (A := 95181996) (B := 1234507656) c383447_0 (rowSum_append (F := f383447) (lo := 271) (n := 151) (m := 602) (A := 240286166) (B := 994221490) c383447_1 (rowSum_append (F := f383447) (lo := 422) (n := 373) (m := 229) (A := 380065976) (B := 614155514) c383447_2 (rowSum_append (F := f383447) (lo := 795) (n := 209) (m := 20) (A := 547497138) (B := 66658376) c383447_3 (c383447_4))))

theorem h383447 : P.leaf 36 383447 = 1329689652 :=
  leaf_weighted (k := 26) (d := 10) (H := 383447) (keep := keep4) (twice := twice4) rows (by decide) (by decide) (bal4) (invRow4 (H := 383447) (by decide) (by decide +kernel)) sum383447

theorem h241515 : P.leaf 36 241515 = 1329689652 :=
  orient6 (v := 383447) (by decide) (by decide +kernel) h383447

theorem cover826811 : P.CoversSplit 26 10 826811 0xfffffffffffffffffefefafa00000000f0f0f0f0e0c0e0c0f0f0f0f000000000fffffffffffffffffafafafa00000000f0f0f0f0e0c0e0c0f0f0f0f000000000fffffffffffffffffefefafa00000000f0f0f0f0c0c0c0c0f0f0f0f000000000fffffffffffffffffafafafa00000000f0f0f0f0c0c0c0c0f0f0f0f000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 629, 636, 922, 929, 930, 1266]) (by decide +kernel)

noncomputable def f826811 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (846654464 + i)

theorem c826811_0 : rowSum f826811 0 358 = 153765532 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 826811) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover826811 (by decide)
  decide +kernel

theorem c826811_1 : rowSum f826811 358 146 = 431782062 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 826811) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover826811 (by decide)
  decide +kernel

theorem c826811_2 : rowSum f826811 504 520 = 422344173 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 826811) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover826811 (by decide)
  decide +kernel

theorem sum826811 : rowSum f826811 0 1024 = 1007891767 :=
  rowSum_append (F := f826811) (lo := 0) (n := 358) (m := 666) (A := 153765532) (B := 854126235) c826811_0 (rowSum_append (F := f826811) (lo := 358) (n := 146) (m := 520) (A := 431782062) (B := 422344173) c826811_1 (c826811_2))

theorem h826811 : P.leaf 36 826811 = 1007891767 :=
  leaf_weighted (k := 26) (d := 10) (H := 826811) (keep := keep4) (twice := twice4) rows (by decide) (by decide) (bal4) (invRow4 (H := 826811) (by decide) (by decide +kernel)) sum826811

theorem h241518 : P.leaf 36 241518 = 1007891767 :=
  orient80 (v := 826811) (by decide) (by decide +kernel) h826811

theorem cover826815 : P.CoversSplit 26 10 826815 0xfffffffffffffffffefefafa00000000ffffffffffccffccfefefafa00000000fffffffffffffffffafafafa00000000ffffffffffccffccfafafafa00000000fffffffffffffffffefefafa00000000ffffffffffccffccfefefafa00000000fffffffffffffffffafafafa00000000ffffffffffccffccfafafafa00000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 629, 636, 922, 930, 1266]) (by decide +kernel)

theorem c826815_0 : P.sumLeaves 26 846658560 182 = 115540916 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 826815) (lo := 0) (len := 182) (W := 115540916) check rows elimOK (by decide) (by decide) cover826815 (by decide)
  decide +kernel

theorem c826815_1 : P.sumLeaves 26 846658742 136 = 172816292 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 826815) (lo := 182) (len := 136) (W := 172816292) check rows elimOK (by decide) (by decide) cover826815 (by decide)
  decide +kernel

theorem c826815_2 : P.sumLeaves 26 846658878 142 = 319046449 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 826815) (lo := 318) (len := 142) (W := 319046449) check rows elimOK (by decide) (by decide) cover826815 (by decide)
  decide +kernel

theorem c826815_3 : P.sumLeaves 26 846659020 144 = 408981075 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 826815) (lo := 460) (len := 144) (W := 408981075) check rows elimOK (by decide) (by decide) cover826815 (by decide)
  decide +kernel

theorem c826815_4 : P.sumLeaves 26 846659164 136 = 352453984 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 826815) (lo := 604) (len := 136) (W := 352453984) check rows elimOK (by decide) (by decide) cover826815 (by decide)
  decide +kernel

theorem c826815_5 : P.sumLeaves 26 846659300 142 = 419094093 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 826815) (lo := 740) (len := 142) (W := 419094093) check rows elimOK (by decide) (by decide) cover826815 (by decide)
  decide +kernel

theorem c826815_6 : P.sumLeaves 26 846659442 134 = 535821103 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 826815) (lo := 882) (len := 134) (W := 535821103) check rows elimOK (by decide) (by decide) cover826815 (by decide)
  decide +kernel

theorem c826815_7 : P.sumLeaves 26 846659576 8 = 74898924 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 826815) (lo := 1016) (len := 8) (W := 74898924) check rows elimOK (by decide) (by decide) cover826815 (by decide)
  decide +kernel

theorem h826815 : P.leaf 36 826815 = 2398652836 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(182, 115540916), (136, 172816292), (142, 319046449), (144, 408981075), (136, 352453984), (142, 419094093), (134, 535821103), (8, 74898924)]) (.cons c826815_0 (.cons c826815_1 (.cons c826815_2 (.cons c826815_3 (.cons c826815_4 (.cons c826815_5 (.cons c826815_6 (.cons c826815_7 (.nil))))))))) (by decide) (by decide))

theorem h241519 : P.leaf 36 241519 = 2398652836 :=
  orient80 (v := 826815) (by decide) (by decide +kernel) h826815

def seg : List (ℕ × ℕ) := [(241503, 180), (241514, 90), (241515, 360), (241518, 360), (241519, 720)]

theorem segOK : checkSeg 20 perms 241503 241534 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 241503 241534 1710 2952461411280 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 2952461411280)
    (SegSum.cons (w := 180) h241503 (SegSum.cons (w := 90) h241514 (SegSum.cons (w := 360) h241515 (SegSum.cons (w := 360) h241518 (SegSum.cons (w := 720) h241519 (show SegSum (P.leaf 36) [] 0 from rfl)))))) (by decide)

end RACert.S6N0.C0.S84
