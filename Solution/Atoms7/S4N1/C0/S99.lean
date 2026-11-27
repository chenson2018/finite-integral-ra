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

namespace RACert.S4N1.C0.S99

open RACert RACert.Problem

theorem cover24575 : P.CoversSplit 24 10 24575 0xfffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaacccccccc88888888cccccccc88888888cccccccc88888888cccccccc88888888fffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaacccccccc88888888cccccccc88888888cccccccc88888888cccccccc88888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [916, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c24575_0 : P.sumLeaves 24 25164800 257 = 70285530 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24575) (lo := 0) (len := 257) (W := 70285530) check rows elimOK (by decide) (by decide) cover24575 (by decide)
  decide +kernel

theorem c24575_1 : P.sumLeaves 24 25165057 119 = 93482609 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24575) (lo := 257) (len := 119) (W := 93482609) check rows elimOK (by decide) (by decide) cover24575 (by decide)
  decide +kernel

theorem c24575_2 : P.sumLeaves 24 25165176 120 = 155747918 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24575) (lo := 376) (len := 120) (W := 155747918) check rows elimOK (by decide) (by decide) cover24575 (by decide)
  decide +kernel

theorem c24575_3 : P.sumLeaves 24 25165296 242 = 177418575 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24575) (lo := 496) (len := 242) (W := 177418575) check rows elimOK (by decide) (by decide) cover24575 (by decide)
  decide +kernel

theorem c24575_4 : P.sumLeaves 24 25165538 134 = 218723312 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24575) (lo := 738) (len := 134) (W := 218723312) check rows elimOK (by decide) (by decide) cover24575 (by decide)
  decide +kernel

theorem c24575_5 : P.sumLeaves 24 25165672 120 = 349910930 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24575) (lo := 872) (len := 120) (W := 349910930) check rows elimOK (by decide) (by decide) cover24575 (by decide)
  decide +kernel

theorem c24575_6 : P.sumLeaves 24 25165792 32 = 163784648 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24575) (lo := 992) (len := 32) (W := 163784648) check rows elimOK (by decide) (by decide) cover24575 (by decide)
  decide +kernel

theorem h24575 : P.leaf 34 24575 = 1229353522 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(257, 70285530), (119, 93482609), (120, 155747918), (242, 177418575), (134, 218723312), (120, 349910930), (32, 163784648)]) (.cons c24575_0 (.cons c24575_1 (.cons c24575_2 (.cons c24575_3 (.cons c24575_4 (.cons c24575_5 (.cons c24575_6 (.nil)))))))) (by decide) (by decide))

theorem cover26092 : P.CoversSplit 24 10 26092 0xf0000000e000aa000000000000000000f0000000000000000000000000000000e0000000e008aa08c0c00000c0c88888e000000000000000c000000000000000f0000000e000a0000000000000000000f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 858, 860, 865, 872, 915]) (by decide +kernel)

noncomputable def f26092 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (26718208 + i)

theorem c26092_0 : rowSum f26092 0 1024 = 4464196 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26092) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover26092 (by decide)
  decide +kernel

theorem sum26092 : rowSum f26092 0 1024 = 4464196 :=
  c26092_0

theorem h26092 : P.leaf 34 26092 = 4464196 :=
  leaf_weighted (k := 24) (d := 10) (H := 26092) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 26092) (by decide) (by decide +kernel)) sum26092

theorem cover26093 : P.CoversSplit 24 10 26093 0xf0000000e000aa000000000000000000f0000000000000000000000000000000f0000000e000aa000000000000000000f0000000000000000000000000000000f0000000e000aa000000000000000000f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 858, 865, 872, 915, 1210, 1259, 1601]) (by decide +kernel)

theorem c26093_0 : P.sumLeaves 24 26719232 1024 = 8863926 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 26093) (lo := 0) (len := 1024) (W := 8863926) check rows elimOK (by decide) (by decide) cover26093 (by decide)
  decide +kernel

theorem h26093 : P.leaf 34 26093 = 8863926 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8863926)]) (.cons c26093_0 (.nil)) (by decide) (by decide))

theorem cover26095 : P.CoversSplit 24 10 26095 0xf0000000f00000000000000000000000f0000000000000000000000000000000f0000000f00000000000000000000000f0000000000000000000000000000000f0000000f00000000000000000000000f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 858, 865, 1202, 1210, 1259, 1601]) (by decide +kernel)

noncomputable def f26095 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (26721280 + i)

theorem c26095_0 : rowSum f26095 0 1024 = 54882283 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26095) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover26095 (by decide)
  decide +kernel

theorem sum26095 : rowSum f26095 0 1024 = 54882283 :=
  c26095_0

theorem h26095 : P.leaf 34 26095 = 54882283 :=
  leaf_weighted (k := 24) (d := 10) (H := 26095) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 26095) (by decide) (by decide +kernel)) sum26095

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
  leaf_weighted (k := 24) (d := 10) (H := 26111) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 26111) (by decide) (by decide +kernel)) sum26111

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
  leaf_weighted (k := 24) (d := 10) (H := 26604) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 26604) (by decide) (by decide +kernel)) sum26604

theorem cover26605 : P.CoversSplit 24 10 26605 0xffffffffeaeaaaaaffffffffeaeaaaaaffffffffea00aa00ffff000000000000ffccffcceac8aa88ccccccccc8c88888ffccffccea00aa00cccc000000000000ffffffffeaeaaaaaffff0000eaea0000ffffffffea00aa00ffff000000000000ffcc0000eac80000cccc0000c8c80000ffcc0000ea000000cccc000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 872, 1202, 1251, 1259, 1264, 1601]) (by decide +kernel)

theorem c26605_0 : P.sumLeaves 24 27243520 364 = 19434889 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 26605) (lo := 0) (len := 364) (W := 19434889) check rows elimOK (by decide) (by decide) cover26605 (by decide)
  decide +kernel

theorem c26605_1 : P.sumLeaves 24 27243884 198 = 54556607 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 26605) (lo := 364) (len := 198) (W := 54556607) check rows elimOK (by decide) (by decide) cover26605 (by decide)
  decide +kernel

theorem c26605_2 : P.sumLeaves 24 27244082 197 = 43694454 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 26605) (lo := 562) (len := 197) (W := 43694454) check rows elimOK (by decide) (by decide) cover26605 (by decide)
  decide +kernel

theorem c26605_3 : P.sumLeaves 24 27244279 181 = 63849654 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 26605) (lo := 759) (len := 181) (W := 63849654) check rows elimOK (by decide) (by decide) cover26605 (by decide)
  decide +kernel

theorem c26605_4 : P.sumLeaves 24 27244460 84 = 97889604 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 26605) (lo := 940) (len := 84) (W := 97889604) check rows elimOK (by decide) (by decide) cover26605 (by decide)
  decide +kernel

theorem h26605 : P.leaf 34 26605 = 279425208 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(364, 19434889), (198, 54556607), (197, 43694454), (181, 63849654), (84, 97889604)]) (.cons c26605_0 (.cons c26605_1 (.cons c26605_2 (.cons c26605_3 (.cons c26605_4 (.nil)))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(24575, 24), (26092, 8), (26093, 24), (26095, 24), (26111, 8), (26604, 8), (26605, 24)]

theorem segOK : checkSeg 16 perms 24575 26607 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 24575 26607 120 47170898208 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 47170898208)
    (SegSum.cons (w := 24) h24575 (SegSum.cons (w := 8) h26092 (SegSum.cons (w := 24) h26093 (SegSum.cons (w := 24) h26095 (SegSum.cons (w := 8) h26111 (SegSum.cons (w := 8) h26604 (SegSum.cons (w := 24) h26605 (show SegSum (P.leaf 34) [] 0 from rfl)))))))) (by decide)

end RACert.S4N1.C0.S99
