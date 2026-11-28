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

namespace RACert.S4N1.C0.S67

open RACert RACert.Problem

theorem cover23406 : P.CoversSplit 24 10 23406 0xffffffffaaaaaaaaffffffffaaaaaaaaf0f0000000000000f0f0000000000000cccccccc88888888cc00cc0088008800c0c0000000000000c000000000000000ffffffffaaaaaaaa0000000000000000f0f055550000000030300000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 522, 859, 879, 1202, 1210, 1259, 1601]) (ps := [(17, [871, 1251], [1259])]) (by decide +kernel)

theorem c23406_0 : P.sumLeaves 24 23967744 742 = 11991485 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23406) (lo := 0) (len := 742) (W := 11991485) check rows elimOK (by decide) (by decide) cover23406 (by decide)
  decide +kernel

theorem c23406_1 : P.sumLeaves 24 23968486 252 = 27234304 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23406) (lo := 742) (len := 252) (W := 27234304) check rows elimOK (by decide) (by decide) cover23406 (by decide)
  decide +kernel

theorem c23406_2 : P.sumLeaves 24 23968738 30 = 20062364 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23406) (lo := 994) (len := 30) (W := 20062364) check rows elimOK (by decide) (by decide) cover23406 (by decide)
  decide +kernel

theorem h23406 : P.leaf 34 23406 = 59288153 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(742, 11991485), (252, 27234304), (30, 20062364)]) (.cons c23406_0 (.cons c23406_1 (.cons c23406_2 (.nil)))) (by decide) (by decide))

theorem h22396 : P.leaf 34 22396 = 59288153 :=
  orient4 (v := 23406) (by decide) (by decide +kernel) h23406

theorem cover23407 : P.CoversSplit 24 10 23407 0xffffffffaaaaaaaaffffffffaaaaaaaaffff000000000000ffff000000000000cccccccc88888888cc00cc0088008800cccc000000000000cc00000000000000ffffffffaaaaaaaa0000000000000000ffff55550000000033330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 1202, 1210, 1259, 1601]) (ps := [(17, [1251], [1259])]) (by decide +kernel)

theorem c23407_0 : P.sumLeaves 24 23968768 682 = 24097523 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23407) (lo := 0) (len := 682) (W := 24097523) check rows elimOK (by decide) (by decide) cover23407 (by decide)
  decide +kernel

theorem c23407_1 : P.sumLeaves 24 23969450 262 = 41062735 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23407) (lo := 682) (len := 262) (W := 41062735) check rows elimOK (by decide) (by decide) cover23407 (by decide)
  decide +kernel

theorem c23407_2 : P.sumLeaves 24 23969712 80 = 68946236 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23407) (lo := 944) (len := 80) (W := 68946236) check rows elimOK (by decide) (by decide) cover23407 (by decide)
  decide +kernel

theorem h23407 : P.leaf 34 23407 = 134106494 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(682, 24097523), (262, 41062735), (80, 68946236)]) (.cons c23407_0 (.cons c23407_1 (.cons c23407_2 (.nil)))) (by decide) (by decide))

theorem h22397 : P.leaf 34 22397 = 134106494 :=
  orient4 (v := 23407) (by decide) (by decide +kernel) h23407

theorem cover23422 : P.CoversSplit 24 10 23422 0xffffffffaaaaaaaaffffffffaaaaaaaaf0f0f5f500000000f0f0f5f500000000cccccccc88888888cc00cc0088008800c0c0c4c400000000c000c40000000000ffffffffaaaaaaaaffffffffaaaaaaaaf0f0f5f500000000f0f0f5f5000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 572, 859, 879, 1202, 1259, 1601]) (by decide +kernel)

theorem c23422_0 : P.sumLeaves 24 23984128 465 = 23391750 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23422) (lo := 0) (len := 465) (W := 23391750) check rows elimOK (by decide) (by decide) cover23422 (by decide)
  decide +kernel

theorem c23422_1 : P.sumLeaves 24 23984593 342 = 38246110 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23422) (lo := 465) (len := 342) (W := 38246110) check rows elimOK (by decide) (by decide) cover23422 (by decide)
  decide +kernel

theorem c23422_2 : P.sumLeaves 24 23984935 180 = 90280686 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23422) (lo := 807) (len := 180) (W := 90280686) check rows elimOK (by decide) (by decide) cover23422 (by decide)
  decide +kernel

theorem c23422_3 : P.sumLeaves 24 23985115 37 = 52889879 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23422) (lo := 987) (len := 37) (W := 52889879) check rows elimOK (by decide) (by decide) cover23422 (by decide)
  decide +kernel

theorem h23422 : P.leaf 34 23422 = 204808425 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(465, 23391750), (342, 38246110), (180, 90280686), (37, 52889879)]) (.cons c23422_0 (.cons c23422_1 (.cons c23422_2 (.cons c23422_3 (.nil))))) (by decide) (by decide))

theorem h22398 : P.leaf 34 22398 = 204808425 :=
  orient4 (v := 23422) (by decide) (by decide +kernel) h23422

theorem cover28539 : P.CoversSplit 24 10 28539 0xfffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafaffccffccfac8fac80000000000000000ffccffccfac8fac80000000000000000fffffffffafafafaffff0000fafa0000ffffffff00000000ffff00000000000000000000000000000000000000000000ffcc0000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [572, 1202, 1210, 1259, 1264, 1308, 1601, 1609]) (by decide +kernel)

theorem c28539_0 : P.sumLeaves 24 29223936 460 = 34469782 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28539) (lo := 0) (len := 460) (W := 34469782) check rows elimOK (by decide) (by decide) cover28539 (by decide)
  decide +kernel

theorem c28539_1 : P.sumLeaves 24 29224396 257 = 63775541 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28539) (lo := 460) (len := 257) (W := 63775541) check rows elimOK (by decide) (by decide) cover28539 (by decide)
  decide +kernel

theorem c28539_2 : P.sumLeaves 24 29224653 121 = 68844951 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28539) (lo := 717) (len := 121) (W := 68844951) check rows elimOK (by decide) (by decide) cover28539 (by decide)
  decide +kernel

theorem c28539_3 : P.sumLeaves 24 29224774 110 = 94590528 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28539) (lo := 838) (len := 110) (W := 94590528) check rows elimOK (by decide) (by decide) cover28539 (by decide)
  decide +kernel

theorem c28539_4 : P.sumLeaves 24 29224884 76 = 160714350 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28539) (lo := 948) (len := 76) (W := 160714350) check rows elimOK (by decide) (by decide) cover28539 (by decide)
  decide +kernel

theorem h28539 : P.leaf 34 28539 = 422395152 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(460, 34469782), (257, 63775541), (121, 68844951), (110, 94590528), (76, 160714350)]) (.cons c28539_0 (.cons c28539_1 (.cons c28539_2 (.cons c28539_3 (.cons c28539_4 (.nil)))))) (by decide) (by decide))

theorem h22399 : P.leaf 34 22399 = 422395152 :=
  orient5 (v := 28539) (by decide) (by decide +kernel) h28539

theorem cover27372 : P.CoversSplit 24 10 27372 0xcc00cc0088008000cc00cc0088008000c400000000000000c400000000000000cc00cc0080008000cc00cc0080008000c400000000000000c400000000000000cc00cc0088008000cc00000088000000c400000000000000c4000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 466, 473, 515, 573, 859, 1202, 1210, 1264, 1601]) (ps := [(18, [524], [1210])]) (by decide +kernel)

theorem c27372_0 : P.sumLeaves 24 28028928 1024 = 7741442 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 27372) (lo := 0) (len := 1024) (W := 7741442) check rows elimOK (by decide) (by decide) cover27372 (by decide)
  decide +kernel

theorem h27372 : P.leaf 34 27372 = 7741442 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 7741442)]) (.cons c27372_0 (.nil)) (by decide) (by decide))

theorem h22444 : P.leaf 34 22444 = 7741442 :=
  orient24 (v := 27372) (by decide) (by decide +kernel) h27372

theorem cover22445 : P.CoversSplit 24 10 22445 0xffffffffeaea0000ffffffffeaea0000aaaaafaf00000000aaaa000000000000cccccccc88880000cccccccc8888000088888c8c000000008888000000000000ff33ff33ea2200000000000000000000aa22af230000000000220000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 517, 522, 860, 916, 1202, 1210, 1251, 1259, 1601]) (by decide +kernel)

theorem c22445_0 : P.sumLeaves 24 22983680 758 = 9663029 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22445) (lo := 0) (len := 758) (W := 9663029) check rows elimOK (by decide) (by decide) cover22445 (by decide)
  decide +kernel

theorem c22445_1 : P.sumLeaves 24 22984438 244 = 20851952 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22445) (lo := 758) (len := 244) (W := 20851952) check rows elimOK (by decide) (by decide) cover22445 (by decide)
  decide +kernel

theorem c22445_2 : P.sumLeaves 24 22984682 22 = 11960246 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22445) (lo := 1002) (len := 22) (W := 11960246) check rows elimOK (by decide) (by decide) cover22445 (by decide)
  decide +kernel

theorem h22445 : P.leaf 34 22445 = 42475227 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(758, 9663029), (244, 20851952), (22, 11960246)]) (.cons c22445_0 (.cons c22445_1 (.cons c22445_2 (.nil)))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(22396, 48), (22397, 48), (22398, 48), (22399, 48), (22444, 48), (22445, 48)]

theorem segOK : checkSeg 16 perms 22396 22446 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 22396 22446 288 41799114864 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 41799114864)
    (SegSum.cons (w := 48) h22396 (SegSum.cons (w := 48) h22397 (SegSum.cons (w := 48) h22398 (SegSum.cons (w := 48) h22399 (SegSum.cons (w := 48) h22444 (SegSum.cons (w := 48) h22445 (show SegSum (P.leaf 34) [] 0 from rfl))))))) (by decide)

end RACert.S4N1.C0.S67
