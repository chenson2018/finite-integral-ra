/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S4N1.C0.Actions

/-! Generated identity-class certificate for the product-row count. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S4N1.C0.S82

open RACert RACert.Problem

theorem cover60399 : P.CoversSplit 24 10 60399 0xfffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaaffccffccfac8aa88ccccccccc8c88888ffccffccfac8aa88ccccccccc8c88888fffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaaffccffccfac8aa88ccccccccc8c88888ffccffccfac8aa88ccccccccc8c88888 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 859, 915, 1202, 1601]) (by decide +kernel)

noncomputable def f60399 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (61848576 + i)

theorem c60399_0 : rowSum f60399 0 226 = 97329296 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 60399) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover60399 (by decide)
  decide +kernel

theorem c60399_1 : rowSum f60399 226 206 = 171165774 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 60399) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover60399 (by decide)
  decide +kernel

theorem c60399_2 : rowSum f60399 432 300 = 303545979 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 60399) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover60399 (by decide)
  decide +kernel

theorem c60399_3 : rowSum f60399 732 292 = 294090823 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 60399) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover60399 (by decide)
  decide +kernel

theorem sum60399 : rowSum f60399 0 1024 = 866131872 :=
  rowSum_append (F := f60399) (lo := 0) (n := 226) (m := 798) (A := 97329296) (B := 768802576) c60399_0 (rowSum_append (F := f60399) (lo := 226) (n := 206) (m := 592) (A := 171165774) (B := 597636802) c60399_1 (rowSum_append (F := f60399) (lo := 432) (n := 300) (m := 292) (A := 303545979) (B := 294090823) c60399_2 (c60399_3)))

theorem h60399 : P.leaf 34 60399 = 866131872 :=
  leaf_weighted (k := 24) (d := 10) (H := 60399) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 60399) (by decide) (by decide +kernel)) sum60399

theorem h24574 : P.leaf 34 24574 = 866131872 :=
  orient24 (v := 60399) (by decide) (by decide +kernel) h60399

theorem cover60415 : P.CoversSplit 24 10 60415 0xfffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaaffccffccfac8aa88ccccccccc8c88888ffccffccfac8aa88ccccccccc8c88888fffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaaffccffccfac8aa88ccccccccc8c88888ffccffccfac8aa88ccccccccc8c88888 :=
  coversSplit check rows (by decide) (by decide) (xs := [859, 915, 1202, 1601]) (by decide +kernel)

noncomputable def f60415 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (61864960 + i)

theorem c60415_0 : rowSum f60415 0 226 = 175721190 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 60415) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover60415 (by decide)
  decide +kernel

theorem c60415_1 : rowSum f60415 226 206 = 282055383 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 60415) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover60415 (by decide)
  decide +kernel

theorem c60415_2 : rowSum f60415 432 300 = 415858812 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 60415) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover60415 (by decide)
  decide +kernel

theorem c60415_3 : rowSum f60415 732 292 = 355718137 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 60415) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover60415 (by decide)
  decide +kernel

theorem sum60415 : rowSum f60415 0 1024 = 1229353522 :=
  rowSum_append (F := f60415) (lo := 0) (n := 226) (m := 798) (A := 175721190) (B := 1053632332) c60415_0 (rowSum_append (F := f60415) (lo := 226) (n := 206) (m := 592) (A := 282055383) (B := 771576949) c60415_1 (rowSum_append (F := f60415) (lo := 432) (n := 300) (m := 292) (A := 415858812) (B := 355718137) c60415_2 (c60415_3)))

theorem h60415 : P.leaf 34 60415 = 1229353522 :=
  leaf_weighted (k := 24) (d := 10) (H := 60415) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 60415) (by decide) (by decide +kernel)) sum60415

theorem h24575 : P.leaf 34 24575 = 1229353522 :=
  orient24 (v := 60415) (by decide) (by decide +kernel) h60415

theorem cover26092 : P.CoversSplit 24 10 26092 0xf0000000e000aa000000000000000000f0000000000000000000000000000000e0000000e008aa08c0c00000c0c88888e000000000000000c000000000000000f0000000e000a0000000000000000000f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 858, 860, 865, 872, 915]) (by decide +kernel)

noncomputable def f26092 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (26718208 + i)

theorem c26092_0 : rowSum f26092 0 1024 = 4464196 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26092) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover26092 (by decide)
  decide +kernel

theorem sum26092 : rowSum f26092 0 1024 = 4464196 :=
  c26092_0

theorem h26092 : P.leaf 34 26092 = 4464196 :=
  leaf_weighted (k := 24) (d := 10) (H := 26092) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 26092) (by decide) (by decide +kernel)) sum26092

theorem cover26108 : P.CoversSplit 24 10 26108 0xf0000000f000aa000000000000000000f0000000000000000000000000000000f0000000f008aa08c0c00000c0c88888f000000000000000c000000000000000f0000000f000a0000000000000000000f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 858, 860, 865, 872, 915, 1202, 1601]) (by decide +kernel)

noncomputable def f26108 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (26734592 + i)

theorem c26108_0 : rowSum f26108 0 1024 = 8863926 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26108) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover26108 (by decide)
  decide +kernel

theorem sum26108 : rowSum f26108 0 1024 = 8863926 :=
  c26108_0

theorem h26108 : P.leaf 34 26108 = 8863926 :=
  leaf_weighted (k := 24) (d := 10) (H := 26108) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 26108) (by decide) (by decide +kernel)) sum26108

theorem h26093 : P.leaf 34 26093 = 8863926 :=
  orient24 (v := 26108) (by decide) (by decide +kernel) h26108

theorem cover26095 : P.CoversSplit 24 10 26095 0xf0000000f00000000000000000000000f0000000000000000000000000000000f0000000f00000000000000000000000f0000000000000000000000000000000f0000000f00000000000000000000000f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 858, 865, 1202, 1210, 1259, 1601]) (by decide +kernel)

noncomputable def f26095 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (26721280 + i)

theorem c26095_0 : rowSum f26095 0 1024 = 54882283 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26095) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover26095 (by decide)
  decide +kernel

theorem sum26095 : rowSum f26095 0 1024 = 54882283 :=
  c26095_0

theorem h26095 : P.leaf 34 26095 = 54882283 :=
  leaf_weighted (k := 24) (d := 10) (H := 26095) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 26095) (by decide) (by decide +kernel)) sum26095

theorem cover26111 : P.CoversSplit 24 10 26111 0xfffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaaffccffccfac8aa88ccccccccc8c88888ffccffccfac8aa88ccccccccc8c88888fffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaaffccffccfac8aa88ccccccccc8c88888ffccffccfac8aa88ccccccccc8c88888 :=
  coversSplit check rows (by decide) (by decide) (xs := [858, 865, 1202, 1259, 1601]) (by decide +kernel)

noncomputable def f26111 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (26737664 + i)

theorem c26111_0 : rowSum f26111 0 226 = 139378972 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26111) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover26111 (by decide)
  decide +kernel

theorem c26111_1 : rowSum f26111 226 206 = 196580746 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26111) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover26111 (by decide)
  decide +kernel

theorem c26111_2 : rowSum f26111 432 300 = 351399335 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26111) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover26111 (by decide)
  decide +kernel

theorem c26111_3 : rowSum f26111 732 292 = 346211028 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26111) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover26111 (by decide)
  decide +kernel

theorem sum26111 : rowSum f26111 0 1024 = 1033570081 :=
  rowSum_append (F := f26111) (lo := 0) (n := 226) (m := 798) (A := 139378972) (B := 894191109) c26111_0 (rowSum_append (F := f26111) (lo := 226) (n := 206) (m := 592) (A := 196580746) (B := 697610363) c26111_1 (rowSum_append (F := f26111) (lo := 432) (n := 300) (m := 292) (A := 351399335) (B := 346211028) c26111_2 (c26111_3)))

theorem h26111 : P.leaf 34 26111 = 1033570081 :=
  leaf_weighted (k := 24) (d := 10) (H := 26111) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 26111) (by decide) (by decide +kernel)) sum26111

theorem cover26604 : P.CoversSplit 24 10 26604 0xffffffffeaeaaaaaffffffffeaeaaaaaffffffffea00aa00ffff000000000000eecceecceac8aa88ccccccccc8c88888eecceeccea00aa00cccc000000000000ffffffffeaeaaaaaffff0000eaea0000ffffffffea00aa00ffff000000000000e0c00000e0c00000c0c00000c0c00000e0c00000e0080000c0c0000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 872, 1251, 1264]) (by decide +kernel)

noncomputable def f26604 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (27242496 + i)

theorem c26604_0 : rowSum f26604 0 475 = 28496895 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26604) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover26604 (by decide)
  decide +kernel

theorem c26604_1 : rowSum f26604 475 469 = 56875019 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26604) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover26604 (by decide)
  decide +kernel

theorem c26604_2 : rowSum f26604 944 80 = 55381268 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26604) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover26604 (by decide)
  decide +kernel

theorem sum26604 : rowSum f26604 0 1024 = 140753182 :=
  rowSum_append (F := f26604) (lo := 0) (n := 475) (m := 549) (A := 28496895) (B := 112256287) c26604_0 (rowSum_append (F := f26604) (lo := 475) (n := 469) (m := 80) (A := 56875019) (B := 55381268) c26604_1 (c26604_2))

theorem h26604 : P.leaf 34 26604 = 140753182 :=
  leaf_weighted (k := 24) (d := 10) (H := 26604) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 26604) (by decide) (by decide +kernel)) sum26604

theorem cover26620 : P.CoversSplit 24 10 26620 0xfffffffffafaaaaafffffffffafaaaaafffffffffa00aa00fffffffffa00aa00ffccffccfac8aa88ccccccccc8c88888ffccffccfa00aa00ccccccccc8008800fffffffffafaaaaafffffffffafaaaaafffffffffa00aa00fffffffffa00aa00f0c0f0c0f0c0a080c0c0c0c0c0c08080f0c0f0c0f008a008c0c0c0c0c0088008 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 872, 1202, 1601]) (by decide +kernel)

noncomputable def f26620 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (27258880 + i)

theorem c26620_0 : rowSum f26620 0 375 = 23552352 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26620) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover26620 (by decide)
  decide +kernel

theorem c26620_1 : rowSum f26620 375 125 = 82513914 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26620) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover26620 (by decide)
  decide +kernel

theorem c26620_2 : rowSum f26620 500 512 = 146396026 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26620) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover26620 (by decide)
  decide +kernel

theorem c26620_3 : rowSum f26620 1012 12 = 26962916 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26620) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover26620 (by decide)
  decide +kernel

theorem sum26620 : rowSum f26620 0 1024 = 279425208 :=
  rowSum_append (F := f26620) (lo := 0) (n := 375) (m := 649) (A := 23552352) (B := 255872856) c26620_0 (rowSum_append (F := f26620) (lo := 375) (n := 125) (m := 524) (A := 82513914) (B := 173358942) c26620_1 (rowSum_append (F := f26620) (lo := 500) (n := 512) (m := 12) (A := 146396026) (B := 26962916) c26620_2 (c26620_3)))

theorem h26620 : P.leaf 34 26620 = 279425208 :=
  leaf_weighted (k := 24) (d := 10) (H := 26620) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 26620) (by decide) (by decide +kernel)) sum26620

theorem h26605 : P.leaf 34 26605 = 279425208 :=
  orient24 (v := 26620) (by decide) (by decide +kernel) h26620

def seg : List (ℕ × ℕ) := [(24574, 24), (24575, 24), (26092, 8), (26093, 24), (26095, 24), (26111, 8), (26604, 8), (26605, 24)]

theorem segOK : checkSeg 16 perms 24574 26607 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 24574 26607 144 67958063136 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 67958063136)
    (SegSum.cons (w := 24) h24574 (SegSum.cons (w := 24) h24575 (SegSum.cons (w := 8) h26092 (SegSum.cons (w := 24) h26093 (SegSum.cons (w := 24) h26095 (SegSum.cons (w := 8) h26111 (SegSum.cons (w := 8) h26604 (SegSum.cons (w := 24) h26605 (show SegSum (P.leaf 34) [] 0 from rfl))))))))) (by decide)

end RACert.S4N1.C0.S82
