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

namespace RACert.S6N0.C0.S110

open RACert RACert.Problem

theorem cover243703 : P.CoversSplit 26 10 243703 0xfffffffffffffffffffffffffffffafaffffffffffffccccffffaaaaffcc8888ffffffffffffffffffffaaaaffffaaaaffffffffffffccccffffaaaaffcc8888fffffffffffffffffffffffffffffafaffffffffccccccccffffaaaacccc8888ffffffffffffffffffffaaaaffffaaaaffffffffccccccccffffaaaacccc8888 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 873, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c243703_0 : P.sumLeaves 26 249551872 148 = 88965087 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243703) (lo := 0) (len := 148) (W := 88965087) check rows elimOK (by decide) (by decide) cover243703 (by decide)
  decide +kernel

theorem c243703_1 : P.sumLeaves 26 249552020 104 = 136612981 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243703) (lo := 148) (len := 104) (W := 136612981) check rows elimOK (by decide) (by decide) cover243703 (by decide)
  decide +kernel

theorem c243703_2 : P.sumLeaves 26 249552124 144 = 447800385 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243703) (lo := 252) (len := 144) (W := 447800385) check rows elimOK (by decide) (by decide) cover243703 (by decide)
  decide +kernel

theorem c243703_3 : P.sumLeaves 26 249552268 96 = 628491103 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243703) (lo := 396) (len := 96) (W := 628491103) check rows elimOK (by decide) (by decide) cover243703 (by decide)
  decide +kernel

theorem c243703_4 : P.sumLeaves 26 249552364 128 = 499557648 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243703) (lo := 492) (len := 128) (W := 499557648) check rows elimOK (by decide) (by decide) cover243703 (by decide)
  decide +kernel

theorem c243703_5 : P.sumLeaves 26 249552492 112 = 422294776 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243703) (lo := 620) (len := 112) (W := 422294776) check rows elimOK (by decide) (by decide) cover243703 (by decide)
  decide +kernel

theorem c243703_6 : P.sumLeaves 26 249552604 128 = 630296535 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243703) (lo := 732) (len := 128) (W := 630296535) check rows elimOK (by decide) (by decide) cover243703 (by decide)
  decide +kernel

theorem c243703_7 : P.sumLeaves 26 249552732 100 = 783672649 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243703) (lo := 860) (len := 100) (W := 783672649) check rows elimOK (by decide) (by decide) cover243703 (by decide)
  decide +kernel

theorem c243703_8 : P.sumLeaves 26 249552832 64 = 631887940 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243703) (lo := 960) (len := 64) (W := 631887940) check rows elimOK (by decide) (by decide) cover243703 (by decide)
  decide +kernel

theorem h243703 : P.leaf 36 243703 = 4269579104 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(148, 88965087), (104, 136612981), (144, 447800385), (96, 628491103), (128, 499557648), (112, 422294776), (128, 630296535), (100, 783672649), (64, 631887940)]) (.cons c243703_0 (.cons c243703_1 (.cons c243703_2 (.cons c243703_3 (.cons c243703_4 (.cons c243703_5 (.cons c243703_6 (.cons c243703_7 (.cons c243703_8 (.nil)))))))))) (by decide) (by decide))

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
  leaf_weighted (k := 26) (d := 10) (H := 243708) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 243708) (by decide) (by decide +kernel)) sum243708

theorem cover243709 : P.CoversSplit 26 10 243709 0xfffffffffffffffffffffffffffffafaffffffffffffccccffffaaaaffcc8888ffffffffffffffffffffaaaaffffaaaaffffffffffffccccffffaaaaffcc8888fffffffffffffffffffffffffffffafaffffffffcc00cc00ffffaaaacc008800ffffffffffffffffffffaaaaffffaaaaffffffffcc00cc00ffffaaaacc008800 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c243709_0 : P.sumLeaves 26 249558016 165 = 118761997 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243709) (lo := 0) (len := 165) (W := 118761997) check rows elimOK (by decide) (by decide) cover243709 (by decide)
  decide +kernel

theorem c243709_1 : P.sumLeaves 26 249558181 132 = 180190774 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243709) (lo := 165) (len := 132) (W := 180190774) check rows elimOK (by decide) (by decide) cover243709 (by decide)
  decide +kernel

theorem c243709_2 : P.sumLeaves 26 249558313 127 = 514839702 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243709) (lo := 297) (len := 127) (W := 514839702) check rows elimOK (by decide) (by decide) cover243709 (by decide)
  decide +kernel

theorem c243709_3 : P.sumLeaves 26 249558440 112 = 781326094 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243709) (lo := 424) (len := 112) (W := 781326094) check rows elimOK (by decide) (by decide) cover243709 (by decide)
  decide +kernel

theorem c243709_4 : P.sumLeaves 26 249558552 120 = 371688620 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243709) (lo := 536) (len := 120) (W := 371688620) check rows elimOK (by decide) (by decide) cover243709 (by decide)
  decide +kernel

theorem c243709_5 : P.sumLeaves 26 249558672 104 = 486466776 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243709) (lo := 656) (len := 104) (W := 486466776) check rows elimOK (by decide) (by decide) cover243709 (by decide)
  decide +kernel

theorem c243709_6 : P.sumLeaves 26 249558776 128 = 730915741 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243709) (lo := 760) (len := 128) (W := 730915741) check rows elimOK (by decide) (by decide) cover243709 (by decide)
  decide +kernel

theorem c243709_7 : P.sumLeaves 26 249558904 100 = 930121578 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243709) (lo := 888) (len := 100) (W := 930121578) check rows elimOK (by decide) (by decide) cover243709 (by decide)
  decide +kernel

theorem c243709_8 : P.sumLeaves 26 249559004 36 = 455787674 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243709) (lo := 988) (len := 36) (W := 455787674) check rows elimOK (by decide) (by decide) cover243709 (by decide)
  decide +kernel

theorem h243709 : P.leaf 36 243709 = 4570098956 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(165, 118761997), (132, 180190774), (127, 514839702), (112, 781326094), (120, 371688620), (104, 486466776), (128, 730915741), (100, 930121578), (36, 455787674)]) (.cons c243709_0 (.cons c243709_1 (.cons c243709_2 (.cons c243709_3 (.cons c243709_4 (.cons c243709_5 (.cons c243709_6 (.cons c243709_7 (.cons c243709_8 (.nil)))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(243703, 720), (243708, 360), (243709, 720)]

theorem segOK : checkSeg 20 perms 243703 243711 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 243703 243711 1800 7075145873520 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 7075145873520)
    (SegSum.cons (w := 720) h243703 (SegSum.cons (w := 360) h243708 (SegSum.cons (w := 720) h243709 (show SegSum (P.leaf 36) [] 0 from rfl)))) (by decide)

end RACert.S6N0.C0.S110
