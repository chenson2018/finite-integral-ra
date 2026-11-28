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

namespace RACert.S4N1.C0.S78

open RACert RACert.Problem

theorem cover28542 : P.CoversSplit 24 10 28542 0xfffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafaffccffccfac8fac80000000000000000ffccffccfac8fac80000000000000000fffffffffafafafaffff0000fafa0000ffffffff00000000ffff00000000000000000000000000000000000000000000ffcc0000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 572, 1202, 1259, 1264, 1308, 1601, 1609]) (by decide +kernel)

noncomputable def f28542 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (29227008 + i)

theorem c28542_0 : rowSum f28542 0 603 = 101547938 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 28542) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover28542 (by decide)
  decide +kernel

theorem c28542_1 : rowSum f28542 603 272 = 121804300 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 28542) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover28542 (by decide)
  decide +kernel

theorem c28542_2 : rowSum f28542 875 149 = 286014790 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 28542) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover28542 (by decide)
  decide +kernel

theorem sum28542 : rowSum f28542 0 1024 = 509367028 :=
  rowSum_append (F := f28542) (lo := 0) (n := 603) (m := 421) (A := 101547938) (B := 407819090) c28542_0 (rowSum_append (F := f28542) (lo := 603) (n := 272) (m := 149) (A := 121804300) (B := 286014790) c28542_1 (c28542_2))

theorem h28542 : P.leaf 34 28542 = 509367028 :=
  leaf_weighted (k := 24) (d := 10) (H := 28542) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 28542) (by decide) (by decide +kernel)) sum28542

theorem h24446 : P.leaf 34 24446 = 509367028 :=
  orient5 (v := 28542) (by decide) (by decide +kernel) h28542

theorem cover28543 : P.CoversSplit 24 10 28543 0xfffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafaffccffccfac8fac80000000000000000ffccffccfac8fac80000000000000000fffffffffafafafaffff0000fafa0000ffffffff00000000ffff00000000000000000000000000000000000000000000ffcc0000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [572, 1202, 1210, 1259, 1264, 1308, 1601, 1609]) (by decide +kernel)

noncomputable def f28543 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (29228032 + i)

theorem c28543_0 : rowSum f28543 0 603 = 132470758 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 28543) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover28543 (by decide)
  decide +kernel

theorem c28543_1 : rowSum f28543 603 272 = 180853928 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 28543) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover28543 (by decide)
  decide +kernel

theorem c28543_2 : rowSum f28543 875 149 = 377308542 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 28543) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover28543 (by decide)
  decide +kernel

theorem sum28543 : rowSum f28543 0 1024 = 690633228 :=
  rowSum_append (F := f28543) (lo := 0) (n := 603) (m := 421) (A := 132470758) (B := 558162470) c28543_0 (rowSum_append (F := f28543) (lo := 603) (n := 272) (m := 149) (A := 180853928) (B := 377308542) c28543_1 (c28543_2))

theorem h28543 : P.leaf 34 28543 = 690633228 :=
  leaf_weighted (k := 24) (d := 10) (H := 28543) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 28543) (by decide) (by decide +kernel)) sum28543

theorem h24447 : P.leaf 34 24447 = 690633228 :=
  orient5 (v := 28543) (by decide) (by decide +kernel) h28543

theorem cover58671 : P.CoversSplit 24 10 58671 0xfffffffffefa0000fffffffffefa000080008400000000008000840000000000ffecffecfee8000000000000000000008000840000000000000000000000000080008000800000008020802080200000800080000000000080008001000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 529, 572, 858, 860, 865, 872, 915, 1202, 1601]) (by decide +kernel)

noncomputable def f58671 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (60079104 + i)

theorem c58671_0 : rowSum f58671 0 1024 = 35572128 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 58671) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover58671 (by decide)
  decide +kernel

theorem sum58671 : rowSum f58671 0 1024 = 35572128 :=
  c58671_0

theorem h58671 : P.leaf 34 58671 = 35572128 :=
  leaf_weighted (k := 24) (d := 10) (H := 58671) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 58671) (by decide) (by decide +kernel)) sum58671

theorem h24485 : P.leaf 34 24485 = 35572128 :=
  orient5 (v := 58671) (by decide) (by decide +kernel) h58671

theorem cover58687 : P.CoversSplit 24 10 58687 0xfffffffffffa0000fffffffffffa0000f000f50000000000f000f50000000000fffcfffcfff800000000000000000000f000f500000000000000000000000000f000f000f0000000f030f030f0300000f000f00000000000f000f001000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 529, 572, 858, 860, 865, 872, 915, 1202, 1601]) (by decide +kernel)

noncomputable def f58687 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (60095488 + i)

theorem c58687_0 : rowSum f58687 0 953 = 93799802 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 58687) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover58687 (by decide)
  decide +kernel

theorem c58687_1 : rowSum f58687 953 71 = 44162324 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 58687) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover58687 (by decide)
  decide +kernel

theorem sum58687 : rowSum f58687 0 1024 = 137962126 :=
  rowSum_append (F := f58687) (lo := 0) (n := 953) (m := 71) (A := 93799802) (B := 44162324) c58687_0 (c58687_1)

theorem h58687 : P.leaf 34 58687 = 137962126 :=
  leaf_weighted (k := 24) (d := 10) (H := 58687) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 58687) (by decide) (by decide +kernel)) sum58687

theorem h24487 : P.leaf 34 24487 = 137962126 :=
  orient5 (v := 58687) (by decide) (by decide +kernel) h58687

theorem cover40395 : P.CoversSplit 24 10 40395 0xaa000000aa0000000000000000000000aa000000000000000000000000000000aa000000aa0000000000000000000000aa000000000000000000000000000000aa000000aa0000000000000000000000aa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [466, 515, 516, 522, 858, 865, 1202, 1209, 1258, 1601]) (by decide +kernel)

noncomputable def f40395 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (41364480 + i)

theorem c40395_0 : rowSum f40395 0 1024 = 9383092 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 40395) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover40395 (by decide)
  decide +kernel

theorem sum40395 : rowSum f40395 0 1024 = 9383092 :=
  c40395_0

theorem h40395 : P.leaf 34 40395 = 9383092 :=
  leaf_weighted (k := 24) (d := 10) (H := 40395) (keep := keep5) (twice := twice5) rows (by decide) (by decide) (bal5) (invRow5 (H := 40395) (by decide) (by decide +kernel)) sum40395

theorem h24490 : P.leaf 34 24490 = 9383092 :=
  orient25 (v := 40395) (by decide) (by decide +kernel) h40395

theorem cover24533 : P.CoversSplit 24 10 24533 0xfffffffff0f0a0a0fffffffff0f0a0a0fffffffff0f0a0a0fffffffff0f0a0a0cccccccc80008000cc00cc0080008000cccccccc80008000cc00cc0080008000ff00ff00f000a000ff33ff33f030a020ff00ff0000000000ff33ff33000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 516, 916, 1202, 1210, 1259, 1601]) (ps := [(8, [615], [1266])]) (by decide +kernel)

theorem c24533_0 : P.sumLeaves 24 25121792 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24533) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover24533 (by decide)
  decide +kernel

theorem contract24533_1 : P.leaf 30 392532 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 475), (8, 0, 1266), (31, 1, 615), (14, 0, 1266), (5, 1, 433), (21, 1, 482), (20, 1, 488), (9, 7, 629), (12, 1, 825), (15, 13, 972)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c24533_1 : P.sumLeaves 24 25122048 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 392532) rows (by decide) (by decide)).symm.trans contract24533_1

theorem contract24533_2 : P.leaf 30 392533 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 475), (29, 1, 916), (8, 0, 1266), (31, 1, 615), (14, 0, 1266), (5, 1, 433), (21, 1, 482), (20, 1, 488), (9, 7, 629), (12, 1, 825), (15, 13, 972)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c24533_2 : P.sumLeaves 24 25122112 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 392533) rows (by decide) (by decide)).symm.trans contract24533_2

theorem c24533_3 : P.sumLeaves 24 25122176 355 = 27669171 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24533) (lo := 384) (len := 355) (W := 27669171) check rows elimOK (by decide) (by decide) cover24533 (by decide)
  decide +kernel

theorem c24533_4 : P.sumLeaves 24 25122531 150 = 30479063 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24533) (lo := 739) (len := 150) (W := 30479063) check rows elimOK (by decide) (by decide) cover24533 (by decide)
  decide +kernel

theorem c24533_5 : P.sumLeaves 24 25122681 135 = 76340989 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24533) (lo := 889) (len := 135) (W := 76340989) check rows elimOK (by decide) (by decide) cover24533 (by decide)
  decide +kernel

theorem h24533 : P.leaf 34 24533 = 134489223 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 0), (64, 0), (355, 27669171), (150, 30479063), (135, 76340989)]) (.cons c24533_0 (.cons c24533_1 (.cons c24533_2 (.cons c24533_3 (.cons c24533_4 (.cons c24533_5 (.nil))))))) (by decide) (by decide))

theorem h24491 : P.leaf 34 24491 = 134489223 :=
  orient4 (v := 24533) (by decide) (by decide +kernel) h24533

theorem cover24492 : P.CoversSplit 24 10 24492 0xaaaa0000aaaaa0a0aaaa0000aaaaa0a0aaaa000000000000aaaa0000000000008888000088888080888800008888808088880000000000008888000000000000aa000000aa00a0000000000000000000aa0000000000000000220000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 517, 522, 916, 1202, 1259, 1601]) (by decide +kernel)

theorem c24492_0 : P.sumLeaves 24 25079808 1017 = 20387359 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24492) (lo := 0) (len := 1017) (W := 20387359) check rows elimOK (by decide) (by decide) cover24492 (by decide)
  decide +kernel

theorem c24492_1 : P.sumLeaves 24 25080825 7 = 5032160 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24492) (lo := 1017) (len := 7) (W := 5032160) check rows elimOK (by decide) (by decide) cover24492 (by decide)
  decide +kernel

theorem h24492 : P.leaf 34 24492 = 25419519 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1017, 20387359), (7, 5032160)]) (.cons c24492_0 (.cons c24492_1 (.nil))) (by decide) (by decide))

theorem cover24493 : P.CoversSplit 24 10 24493 0xffffffffeaeaa0a0ffffffffeaeaa0a0ffffffffeaeaa0a0ffffffffeaeaa0a0cccccccc88888080cccccccc88888080cccccccc88888080cccccccc88888080ff00ff00ea00a0000000000000000000ff00ff00ea00a00000330033002200200000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 916, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c24493_0 : P.sumLeaves 24 25080832 631 = 15224232 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24493) (lo := 0) (len := 631) (W := 15224232) check rows elimOK (by decide) (by decide) cover24493 (by decide)
  decide +kernel

theorem c24493_1 : P.sumLeaves 24 25081463 208 = 32328567 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24493) (lo := 631) (len := 208) (W := 32328567) check rows elimOK (by decide) (by decide) cover24493 (by decide)
  decide +kernel

theorem c24493_2 : P.sumLeaves 24 25081671 140 = 49902659 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24493) (lo := 839) (len := 140) (W := 49902659) check rows elimOK (by decide) (by decide) cover24493 (by decide)
  decide +kernel

theorem c24493_3 : P.sumLeaves 24 25081811 45 = 43738790 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24493) (lo := 979) (len := 45) (W := 43738790) check rows elimOK (by decide) (by decide) cover24493 (by decide)
  decide +kernel

theorem h24493 : P.leaf 34 24493 = 141194248 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(631, 15224232), (208, 32328567), (140, 49902659), (45, 43738790)]) (.cons c24493_0 (.cons c24493_1 (.cons c24493_2 (.cons c24493_3 (.nil))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(24446, 24), (24447, 24), (24485, 12), (24487, 24), (24490, 24), (24491, 48), (24492, 48), (24493, 48)]

theorem segOK : checkSeg 16 perms 24446 24494 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 24446 24494 252 47216100432 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 47216100432)
    (SegSum.cons (w := 24) h24446 (SegSum.cons (w := 24) h24447 (SegSum.cons (w := 12) h24485 (SegSum.cons (w := 24) h24487 (SegSum.cons (w := 24) h24490 (SegSum.cons (w := 48) h24491 (SegSum.cons (w := 48) h24492 (SegSum.cons (w := 48) h24493 (show SegSum (P.leaf 34) [] 0 from rfl))))))))) (by decide)

end RACert.S4N1.C0.S78
