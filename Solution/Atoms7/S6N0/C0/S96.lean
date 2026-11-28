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

namespace RACert.S6N0.C0.S96

open RACert RACert.Problem

theorem cover384983 : P.CoversSplit 26 10 384983 0xfffffffffffffffffffffffffffffffffffffffffffffffffafafafac8c8c8c8fffffffffffffffffafafafafafafafafffffffffffffffffafafafac8c8c8c8ffffffffffffffffffffffffffffffffffffffffccccccccfafafafac8c8c8c8fffffffffffffffffafafafafafafafaffffffffccccccccfafafafac8c8c8c8 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 1658, 1665]) (by decide +kernel)

noncomputable def f384983 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (394222592 + i)

theorem c384983_0 : rowSum f384983 0 229 = 907370336 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 384983) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover384983 (by decide)
  decide +kernel

theorem c384983_1 : rowSum f384983 229 158 = 1118027852 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 384983) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover384983 (by decide)
  decide +kernel

theorem c384983_2 : rowSum f384983 387 96 = 1449894284 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 384983) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover384983 (by decide)
  decide +kernel

theorem c384983_3 : rowSum f384983 483 395 = 1609682758 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 384983) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover384983 (by decide)
  decide +kernel

theorem c384983_4 : rowSum f384983 878 146 = 1163020060 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 384983) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover384983 (by decide)
  decide +kernel

theorem sum384983 : rowSum f384983 0 1024 = 6247995290 :=
  rowSum_append (F := f384983) (lo := 0) (n := 229) (m := 795) (A := 907370336) (B := 5340624954) c384983_0 (rowSum_append (F := f384983) (lo := 229) (n := 158) (m := 637) (A := 1118027852) (B := 4222597102) c384983_1 (rowSum_append (F := f384983) (lo := 387) (n := 96) (m := 541) (A := 1449894284) (B := 2772702818) c384983_2 (rowSum_append (F := f384983) (lo := 483) (n := 395) (m := 146) (A := 1609682758) (B := 1163020060) c384983_3 (c384983_4))))

theorem h384983 : P.leaf 36 384983 = 6247995290 :=
  leaf_weighted (k := 26) (d := 10) (H := 384983) (keep := keep4) (twice := twice4) rows (by decide) (by decide) (bal4) (invRow4 (H := 384983) (by decide) (by decide +kernel)) sum384983

theorem h245739 : P.leaf 36 245739 = 6247995290 :=
  orient6 (v := 384983) (by decide) (by decide +kernel) h384983

theorem cover384990 : P.CoversSplit 26 10 384990 0xfffffffffffffffffffffffffffffffffffffffffffffffffafafafac8c8c8c8fffffffffffffffffafaaaaafafaaaaafffffffffffffffffafaaaaac8c88888ffffffffffffffffffffffffffffffffffffffffccccccccfafafafac8c8c8c8fffffffffffffffffafaaaaafafaaaaaffffffffccccccccfafaaaaac8c88888 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 1273, 1658, 1665]) (by decide +kernel)

theorem c384990_0 : P.sumLeaves 26 394229760 158 = 248241322 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 384990) (lo := 0) (len := 158) (W := 248241322) check rows elimOK (by decide) (by decide) cover384990 (by decide)
  decide +kernel

theorem c384990_1 : P.sumLeaves 26 394229918 128 = 445631399 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 384990) (lo := 158) (len := 128) (W := 445631399) check rows elimOK (by decide) (by decide) cover384990 (by decide)
  decide +kernel

theorem c384990_2 : P.sumLeaves 26 394230046 120 = 410868107 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 384990) (lo := 286) (len := 120) (W := 410868107) check rows elimOK (by decide) (by decide) cover384990 (by decide)
  decide +kernel

theorem c384990_3 : P.sumLeaves 26 394230166 96 = 790972023 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 384990) (lo := 406) (len := 96) (W := 790972023) check rows elimOK (by decide) (by decide) cover384990 (by decide)
  decide +kernel

theorem c384990_4 : P.sumLeaves 26 394230262 130 = 525856102 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 384990) (lo := 502) (len := 130) (W := 525856102) check rows elimOK (by decide) (by decide) cover384990 (by decide)
  decide +kernel

theorem c384990_5 : P.sumLeaves 26 394230392 120 = 683710575 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 384990) (lo := 632) (len := 120) (W := 683710575) check rows elimOK (by decide) (by decide) cover384990 (by decide)
  decide +kernel

theorem c384990_6 : P.sumLeaves 26 394230512 124 = 626540352 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 384990) (lo := 752) (len := 124) (W := 626540352) check rows elimOK (by decide) (by decide) cover384990 (by decide)
  decide +kernel

theorem c384990_7 : P.sumLeaves 26 394230636 96 = 726729735 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 384990) (lo := 876) (len := 96) (W := 726729735) check rows elimOK (by decide) (by decide) cover384990 (by decide)
  decide +kernel

theorem c384990_8 : P.sumLeaves 26 394230732 52 = 686825350 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 384990) (lo := 972) (len := 52) (W := 686825350) check rows elimOK (by decide) (by decide) cover384990 (by decide)
  decide +kernel

theorem h384990 : P.leaf 36 384990 = 5145374965 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(158, 248241322), (128, 445631399), (120, 410868107), (96, 790972023), (130, 525856102), (120, 683710575), (124, 626540352), (96, 726729735), (52, 686825350)]) (.cons c384990_0 (.cons c384990_1 (.cons c384990_2 (.cons c384990_3 (.cons c384990_4 (.cons c384990_5 (.cons c384990_6 (.cons c384990_7 (.cons c384990_8 (.nil)))))))))) (by decide) (by decide))

theorem h245742 : P.leaf 36 245742 = 5145374965 :=
  orient6 (v := 384990) (by decide) (by decide +kernel) h384990

theorem cover384991 : P.CoversSplit 26 10 384991 0xfffffffffffffffffffffffffffffffffffffffffffffffffafafafac8c8c8c8fffffffffffffffffafafafafafafafafffffffffffffffffafafafac8c8c8c8ffffffffffffffffffffffffffffffffffffffffccccccccfafafafac8c8c8c8fffffffffffffffffafafafafafafafaffffffffccccccccfafafafac8c8c8c8 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 1273, 1658, 1665]) (by decide +kernel)

theorem c384991_0 : P.sumLeaves 26 394230784 145 = 589314100 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 384991) (lo := 0) (len := 145) (W := 589314100) check rows elimOK (by decide) (by decide) cover384991 (by decide)
  decide +kernel

theorem c384991_1 : P.sumLeaves 26 394230929 107 = 853669405 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 384991) (lo := 145) (len := 107) (W := 853669405) check rows elimOK (by decide) (by decide) cover384991 (by decide)
  decide +kernel

theorem c384991_2 : P.sumLeaves 26 394231036 140 = 826978607 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 384991) (lo := 252) (len := 140) (W := 826978607) check rows elimOK (by decide) (by decide) cover384991 (by decide)
  decide +kernel

theorem c384991_3 : P.sumLeaves 26 394231176 96 = 1029524634 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 384991) (lo := 392) (len := 96) (W := 1029524634) check rows elimOK (by decide) (by decide) cover384991 (by decide)
  decide +kernel

theorem c384991_4 : P.sumLeaves 26 394231272 124 = 972619197 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 384991) (lo := 488) (len := 124) (W := 972619197) check rows elimOK (by decide) (by decide) cover384991 (by decide)
  decide +kernel

theorem c384991_5 : P.sumLeaves 26 394231396 112 = 962301097 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 384991) (lo := 612) (len := 112) (W := 962301097) check rows elimOK (by decide) (by decide) cover384991 (by decide)
  decide +kernel

theorem c384991_6 : P.sumLeaves 26 394231508 124 = 1144129542 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 384991) (lo := 724) (len := 124) (W := 1144129542) check rows elimOK (by decide) (by decide) cover384991 (by decide)
  decide +kernel

theorem c384991_7 : P.sumLeaves 26 394231632 96 = 1024860567 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 384991) (lo := 848) (len := 96) (W := 1024860567) check rows elimOK (by decide) (by decide) cover384991 (by decide)
  decide +kernel

theorem c384991_8 : P.sumLeaves 26 394231728 80 = 1293200507 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 384991) (lo := 944) (len := 80) (W := 1293200507) check rows elimOK (by decide) (by decide) cover384991 (by decide)
  decide +kernel

theorem h384991 : P.leaf 36 384991 = 8696597656 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(145, 589314100), (107, 853669405), (140, 826978607), (96, 1029524634), (124, 972619197), (112, 962301097), (124, 1144129542), (96, 1024860567), (80, 1293200507)]) (.cons c384991_0 (.cons c384991_1 (.cons c384991_2 (.cons c384991_3 (.cons c384991_4 (.cons c384991_5 (.cons c384991_6 (.cons c384991_7 (.cons c384991_8 (.nil)))))))))) (by decide) (by decide))

theorem h245743 : P.leaf 36 245743 = 8696597656 :=
  orient6 (v := 384991) (by decide) (by decide +kernel) h384991

def seg : List (ℕ × ℕ) := [(245739, 360), (245742, 720), (245743, 720)]

theorem segOK : checkSeg 20 perms 245739 245758 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 245739 245758 1800 12215498591520 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 12215498591520)
    (SegSum.cons (w := 360) h245739 (SegSum.cons (w := 720) h245742 (SegSum.cons (w := 720) h245743 (show SegSum (P.leaf 36) [] 0 from rfl)))) (by decide)

end RACert.S6N0.C0.S96
