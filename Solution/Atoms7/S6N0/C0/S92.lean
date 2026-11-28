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

namespace RACert.S6N0.C0.S92

open RACert RACert.Problem

theorem cover359417 : P.CoversSplit 26 10 359417 0xfffffffffffffffffffffffafffffffafffffffffff0fff0fafafafafac0fac0fffffafafffffafafafafafafafafafafffffafafff0faf0fafafafafac0fac0fffffffffffffffffffffffafffffffaffffffffcc00cc00fafafafac800c8000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 923, 972, 979, 1273, 1658, 1665]) (by decide +kernel)

noncomputable def f359417 (i : ℕ) := rowWeight keep14 twice14 i * P.leaf 26 (368043008 + i)

theorem c359417_0 : rowSum f359417 0 412 = 314991156 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 359417) (keep := keep14) (twice := twice14) check rows elimOK (by decide) (by decide) cover359417 (by decide)
  decide +kernel

theorem c359417_1 : rowSum f359417 412 98 = 741176430 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 359417) (keep := keep14) (twice := twice14) check rows elimOK (by decide) (by decide) cover359417 (by decide)
  decide +kernel

theorem c359417_2 : rowSum f359417 510 416 = 602790716 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 359417) (keep := keep14) (twice := twice14) check rows elimOK (by decide) (by decide) cover359417 (by decide)
  decide +kernel

theorem c359417_3 : rowSum f359417 926 98 = 331813475 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 359417) (keep := keep14) (twice := twice14) check rows elimOK (by decide) (by decide) cover359417 (by decide)
  decide +kernel

theorem sum359417 : rowSum f359417 0 1024 = 1990771777 :=
  rowSum_append (F := f359417) (lo := 0) (n := 412) (m := 612) (A := 314991156) (B := 1675780621) c359417_0 (rowSum_append (F := f359417) (lo := 412) (n := 98) (m := 514) (A := 741176430) (B := 934604191) c359417_1 (rowSum_append (F := f359417) (lo := 510) (n := 416) (m := 98) (A := 602790716) (B := 331813475) c359417_2 (c359417_3)))

theorem h359417 : P.leaf 36 359417 = 1990771777 :=
  leaf_weighted (k := 26) (d := 10) (H := 359417) (keep := keep14) (twice := twice14) rows (by decide) (by decide) (bal14) (invRow14 (H := 359417) (by decide) (by decide +kernel)) sum359417

theorem h243702 : P.leaf 36 243702 = 1990771777 :=
  orient74 (v := 359417) (by decide) (by decide +kernel) h359417

theorem cover359421 : P.CoversSplit 26 10 359421 0xfffffffffffffffffffffffafffffffafffffffffffcfffcfafafafafac8fac8fffffffffffffffffafafafafafafafafffffffffffcfffcfafafafafac8fac8fffffffffffffffffffffffafffffffaffffffffccccccccfafafafac8c8c8c80000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [923, 972, 979, 1273, 1658, 1665]) (by decide +kernel)

theorem c359421_0 : P.sumLeaves 26 368047104 398 = 283391225 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 359421) (lo := 0) (len := 398) (W := 283391225) check rows elimOK (by decide) (by decide) cover359421 (by decide)
  decide +kernel

theorem c359421_1 : P.sumLeaves 26 368047502 98 = 659831272 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 359421) (lo := 398) (len := 98) (W := 659831272) check rows elimOK (by decide) (by decide) cover359421 (by decide)
  decide +kernel

theorem c359421_2 : P.sumLeaves 26 368047600 122 = 438867729 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 359421) (lo := 496) (len := 122) (W := 438867729) check rows elimOK (by decide) (by decide) cover359421 (by decide)
  decide +kernel

theorem c359421_3 : P.sumLeaves 26 368047722 112 = 572825390 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 359421) (lo := 618) (len := 112) (W := 572825390) check rows elimOK (by decide) (by decide) cover359421 (by decide)
  decide +kernel

theorem c359421_4 : P.sumLeaves 26 368047834 122 = 633265643 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 359421) (lo := 730) (len := 122) (W := 633265643) check rows elimOK (by decide) (by decide) cover359421 (by decide)
  decide +kernel

theorem c359421_5 : P.sumLeaves 26 368047956 100 = 703832107 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 359421) (lo := 852) (len := 100) (W := 703832107) check rows elimOK (by decide) (by decide) cover359421 (by decide)
  decide +kernel

theorem c359421_6 : P.sumLeaves 26 368048056 72 = 977565738 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 359421) (lo := 952) (len := 72) (W := 977565738) check rows elimOK (by decide) (by decide) cover359421 (by decide)
  decide +kernel

theorem h359421 : P.leaf 36 359421 = 4269579104 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(398, 283391225), (98, 659831272), (122, 438867729), (112, 572825390), (122, 633265643), (100, 703832107), (72, 977565738)]) (.cons c359421_0 (.cons c359421_1 (.cons c359421_2 (.cons c359421_3 (.cons c359421_4 (.cons c359421_5 (.cons c359421_6 (.nil)))))))) (by decide) (by decide))

theorem h243703 : P.leaf 36 243703 = 4269579104 :=
  orient74 (v := 359421) (by decide) (by decide +kernel) h359421

theorem cover243708 : P.CoversSplit 26 10 243708 0xfffffffffffffffffffffffffffffafaffffffffffffccccffffaaaaffcc8888ffffffffffffffffffffa0a0ffffa0a0ffffffffffffccccffffa0a0ffcc8080fffffffffffffffffffffffffffffafaffffffffcc00cc00ffffaaaacc008800ffffffffffffffffffffa0a0ffffa0a0ffffffffcc00cc00ffffa0a0cc008000 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f243708 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 26 (249556992 + i)

theorem c243708_0 : rowSum f243708 0 287 = 58039510 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 243708) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover243708 (by decide)
  decide +kernel

theorem c243708_1 : rowSum f243708 287 132 = 300010794 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 243708) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover243708 (by decide)
  decide +kernel

theorem c243708_2 : rowSum f243708 419 367 = 560211680 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 243708) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover243708 (by decide)
  decide +kernel

theorem c243708_3 : rowSum f243708 786 166 = 718720302 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 243708) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover243708 (by decide)
  decide +kernel

theorem c243708_4 : rowSum f243708 952 72 = 336844576 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 243708) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover243708 (by decide)
  decide +kernel

theorem sum243708 : rowSum f243708 0 1024 = 1973826862 :=
  rowSum_append (F := f243708) (lo := 0) (n := 287) (m := 737) (A := 58039510) (B := 1915787352) c243708_0 (rowSum_append (F := f243708) (lo := 287) (n := 132) (m := 605) (A := 300010794) (B := 1615776558) c243708_1 (rowSum_append (F := f243708) (lo := 419) (n := 367) (m := 238) (A := 560211680) (B := 1055564878) c243708_2 (rowSum_append (F := f243708) (lo := 786) (n := 166) (m := 72) (A := 718720302) (B := 336844576) c243708_3 (c243708_4))))

theorem h243708 : P.leaf 36 243708 = 1973826862 :=
  leaf_weighted (k := 26) (d := 10) (H := 243708) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 243708) (by decide) (by decide +kernel)) sum243708

theorem cover802783 : P.CoversSplit 26 10 802783 0xfffffffafffffffafffffafafffffafaffff0000ffcc0000ffff0000ffcc0000fffffafafffffafafffffafafffffafaffff0000ffcc0000ffff0000ffcc0000fffffffafffffffafffffafafffffafaffff0000ffcc0000ffff0000ffcc0000fffffafafffffafafffffafafffffafaffff0000ffcc0000ffff0000ffcc0000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 930, 972, 979, 1265, 1272, 1273]) (by decide +kernel)

theorem c802783_0 : P.sumLeaves 26 822049792 176 = 286398427 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 802783) (lo := 0) (len := 176) (W := 286398427) check rows elimOK (by decide) (by decide) cover802783 (by decide)
  decide +kernel

theorem c802783_1 : P.sumLeaves 26 822049968 140 = 443673766 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 802783) (lo := 176) (len := 140) (W := 443673766) check rows elimOK (by decide) (by decide) cover802783 (by decide)
  decide +kernel

theorem c802783_2 : P.sumLeaves 26 822050108 142 = 650625234 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 802783) (lo := 316) (len := 142) (W := 650625234) check rows elimOK (by decide) (by decide) cover802783 (by decide)
  decide +kernel

theorem c802783_3 : P.sumLeaves 26 822050250 170 = 725723472 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 802783) (lo := 458) (len := 170) (W := 725723472) check rows elimOK (by decide) (by decide) cover802783 (by decide)
  decide +kernel

theorem c802783_4 : P.sumLeaves 26 822050420 109 = 673023786 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 802783) (lo := 628) (len := 109) (W := 673023786) check rows elimOK (by decide) (by decide) cover802783 (by decide)
  decide +kernel

theorem c802783_5 : P.sumLeaves 26 822050529 175 = 737180584 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 802783) (lo := 737) (len := 175) (W := 737180584) check rows elimOK (by decide) (by decide) cover802783 (by decide)
  decide +kernel

theorem c802783_6 : P.sumLeaves 26 822050704 104 = 918658667 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 802783) (lo := 912) (len := 104) (W := 918658667) check rows elimOK (by decide) (by decide) cover802783 (by decide)
  decide +kernel

theorem c802783_7 : P.sumLeaves 26 822050808 8 = 134815020 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 802783) (lo := 1016) (len := 8) (W := 134815020) check rows elimOK (by decide) (by decide) cover802783 (by decide)
  decide +kernel

theorem h802783 : P.leaf 36 802783 = 4570098956 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(176, 286398427), (140, 443673766), (142, 650625234), (170, 725723472), (109, 673023786), (175, 737180584), (104, 918658667), (8, 134815020)]) (.cons c802783_0 (.cons c802783_1 (.cons c802783_2 (.cons c802783_3 (.cons c802783_4 (.cons c802783_5 (.cons c802783_6 (.cons c802783_7 (.nil))))))))) (by decide) (by decide))

theorem h243709 : P.leaf 36 243709 = 4570098956 :=
  orient86 (v := 802783) (by decide) (by decide +kernel) h802783

def seg : List (ℕ × ℕ) := [(243702, 360), (243703, 720), (243708, 360), (243709, 720)]

theorem segOK : checkSeg 20 perms 243702 243711 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 243702 243711 2160 7791823713240 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 7791823713240)
    (SegSum.cons (w := 360) h243702 (SegSum.cons (w := 720) h243703 (SegSum.cons (w := 360) h243708 (SegSum.cons (w := 720) h243709 (show SegSum (P.leaf 36) [] 0 from rfl))))) (by decide)

end RACert.S6N0.C0.S92
