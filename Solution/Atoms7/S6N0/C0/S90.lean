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

namespace RACert.S6N0.C0.S90

open RACert RACert.Problem

theorem cover243583 : P.CoversSplit 26 10 243583 0xfffffffffffffffffffffffffffffafaffffffffffffccccffffaaaaff008800ffffffffffffffffffffaaaaffffaaaaffffffffffffccccffffaaaaff008800fffffffffffffffffffffffffffffafaffffffffcc00cc00ffffaaaacc008800ffffffffffffffffffffaaaaffffaaaaffffffffcc00cc00ffffaaaacc008800 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c243583_0 : P.sumLeaves 26 249428992 165 = 259517749 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243583) (lo := 0) (len := 165) (W := 259517749) check rows elimOK (by decide) (by decide) cover243583 (by decide)
  decide +kernel

theorem c243583_1 : P.sumLeaves 26 249429157 132 = 388682611 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243583) (lo := 165) (len := 132) (W := 388682611) check rows elimOK (by decide) (by decide) cover243583 (by decide)
  decide +kernel

theorem c243583_2 : P.sumLeaves 26 249429289 127 = 538473219 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243583) (lo := 297) (len := 127) (W := 538473219) check rows elimOK (by decide) (by decide) cover243583 (by decide)
  decide +kernel

theorem c243583_3 : P.sumLeaves 26 249429416 118 = 781621998 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243583) (lo := 424) (len := 118) (W := 781621998) check rows elimOK (by decide) (by decide) cover243583 (by decide)
  decide +kernel

theorem c243583_4 : P.sumLeaves 26 249429534 120 = 534163287 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243583) (lo := 542) (len := 120) (W := 534163287) check rows elimOK (by decide) (by decide) cover243583 (by decide)
  decide +kernel

theorem c243583_5 : P.sumLeaves 26 249429654 104 = 738781330 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243583) (lo := 662) (len := 104) (W := 738781330) check rows elimOK (by decide) (by decide) cover243583 (by decide)
  decide +kernel

theorem c243583_6 : P.sumLeaves 26 249429758 136 = 730461001 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243583) (lo := 766) (len := 136) (W := 730461001) check rows elimOK (by decide) (by decide) cover243583 (by decide)
  decide +kernel

theorem c243583_7 : P.sumLeaves 26 249429894 98 = 859964285 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243583) (lo := 902) (len := 98) (W := 859964285) check rows elimOK (by decide) (by decide) cover243583 (by decide)
  decide +kernel

theorem c243583_8 : P.sumLeaves 26 249429992 24 = 334577398 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243583) (lo := 1000) (len := 24) (W := 334577398) check rows elimOK (by decide) (by decide) cover243583 (by decide)
  decide +kernel

theorem h243583 : P.leaf 36 243583 = 5166242878 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(165, 259517749), (132, 388682611), (127, 538473219), (118, 781621998), (120, 534163287), (104, 738781330), (136, 730461001), (98, 859964285), (24, 334577398)]) (.cons c243583_0 (.cons c243583_1 (.cons c243583_2 (.cons c243583_3 (.cons c243583_4 (.cons c243583_5 (.cons c243583_6 (.cons c243583_7 (.cons c243583_8 (.nil)))))))))) (by decide) (by decide))

theorem cover359381 : P.CoversSplit 26 10 359381 0xfffffffffffffffffffffff0fffffff0fffffffffffcfffcfafafaf0fac8fac0fffffffffffffffffafaf0f0fafaf0f0fffffffffffcfffcfafaf0f0fac8f0c0ffffffffffccffccfffffff0ffccffc0ffffffffccccccccfafafaf0c8c8c8c00000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 923, 972, 979, 1273, 1658, 1665]) (by decide +kernel)

noncomputable def f359381 (i : ℕ) := rowWeight keep13 twice13 i * P.leaf 26 (368006144 + i)

theorem c359381_0 : rowSum f359381 0 494 = 275236790 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 359381) (keep := keep13) (twice := twice13) check rows elimOK (by decide) (by decide) cover359381 (by decide)
  decide +kernel

theorem c359381_1 : rowSum f359381 494 208 = 324568862 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 359381) (keep := keep13) (twice := twice13) check rows elimOK (by decide) (by decide) cover359381 (by decide)
  decide +kernel

theorem c359381_2 : rowSum f359381 702 206 = 445148544 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 359381) (keep := keep13) (twice := twice13) check rows elimOK (by decide) (by decide) cover359381 (by decide)
  decide +kernel

theorem c359381_3 : rowSum f359381 908 116 = 297302792 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 359381) (keep := keep13) (twice := twice13) check rows elimOK (by decide) (by decide) cover359381 (by decide)
  decide +kernel

theorem sum359381 : rowSum f359381 0 1024 = 1342256988 :=
  rowSum_append (F := f359381) (lo := 0) (n := 494) (m := 530) (A := 275236790) (B := 1067020198) c359381_0 (rowSum_append (F := f359381) (lo := 494) (n := 208) (m := 322) (A := 324568862) (B := 742451336) c359381_1 (rowSum_append (F := f359381) (lo := 702) (n := 206) (m := 116) (A := 445148544) (B := 297302792) c359381_2 (c359381_3)))

theorem h359381 : P.leaf 36 359381 = 1342256988 :=
  leaf_weighted (k := 26) (d := 10) (H := 359381) (keep := keep13) (twice := twice13) rows (by decide) (by decide) (bal13) (invRow13 (H := 359381) (by decide) (by decide +kernel)) sum359381

theorem h243683 : P.leaf 36 243683 = 1342256988 :=
  orient4 (v := 359381) (by decide) (by decide +kernel) h359381

theorem cover359389 : P.CoversSplit 26 10 359389 0xfffffffffffffffffffffffafffffffafffffffffffcfffcfafafafafac8fac8fffffffffffffffffafafafafafafafafffffffffffcfffcfafafafafac8fac8fffffffffffffffffffffffafffffffaffffffffccccccccfafafafac8c8c8c80000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 923, 972, 979, 1273, 1658, 1665]) (by decide +kernel)

theorem c359389_0 : P.sumLeaves 26 368014336 398 = 142367487 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 359389) (lo := 0) (len := 398) (W := 142367487) check rows elimOK (by decide) (by decide) cover359389 (by decide)
  decide +kernel

theorem c359389_1 : P.sumLeaves 26 368014734 98 = 327217179 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 359389) (lo := 398) (len := 98) (W := 327217179) check rows elimOK (by decide) (by decide) cover359389 (by decide)
  decide +kernel

theorem c359389_2 : P.sumLeaves 26 368014832 122 = 285680473 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 359389) (lo := 496) (len := 122) (W := 285680473) check rows elimOK (by decide) (by decide) cover359389 (by decide)
  decide +kernel

theorem c359389_3 : P.sumLeaves 26 368014954 112 = 417782255 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 359389) (lo := 618) (len := 112) (W := 417782255) check rows elimOK (by decide) (by decide) cover359389 (by decide)
  decide +kernel

theorem c359389_4 : P.sumLeaves 26 368015066 122 = 458649031 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 359389) (lo := 730) (len := 122) (W := 458649031) check rows elimOK (by decide) (by decide) cover359389 (by decide)
  decide +kernel

theorem c359389_5 : P.sumLeaves 26 368015188 100 = 504621514 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 359389) (lo := 852) (len := 100) (W := 504621514) check rows elimOK (by decide) (by decide) cover359389 (by decide)
  decide +kernel

theorem c359389_6 : P.sumLeaves 26 368015288 72 = 735510168 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 359389) (lo := 952) (len := 72) (W := 735510168) check rows elimOK (by decide) (by decide) cover359389 (by decide)
  decide +kernel

theorem h359389 : P.leaf 36 359389 = 2871828107 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(398, 142367487), (98, 327217179), (122, 285680473), (112, 417782255), (122, 458649031), (100, 504621514), (72, 735510168)]) (.cons c359389_0 (.cons c359389_1 (.cons c359389_2 (.cons c359389_3 (.cons c359389_4 (.cons c359389_5 (.cons c359389_6 (.nil)))))))) (by decide) (by decide))

theorem h243687 : P.leaf 36 243687 = 2871828107 :=
  orient74 (v := 359389) (by decide) (by decide +kernel) h359389

def seg : List (ℕ × ℕ) := [(243583, 720), (243683, 120), (243687, 720)]

theorem segOK : checkSeg 20 perms 243583 243693 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 243583 243693 1560 5948481947760 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 5948481947760)
    (SegSum.cons (w := 720) h243583 (SegSum.cons (w := 120) h243683 (SegSum.cons (w := 720) h243687 (show SegSum (P.leaf 36) [] 0 from rfl)))) (by decide)

end RACert.S6N0.C0.S90
