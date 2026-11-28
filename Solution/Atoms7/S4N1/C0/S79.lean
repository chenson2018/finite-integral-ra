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

namespace RACert.S4N1.C0.S79

open RACert RACert.Problem

theorem cover24494 : P.CoversSplit 24 10 24494 0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa000000000000aaaa0000000000008888000088880000888800008888000088880000000000008888000000000000aaaa0000aaaa00000000000000000000aaaa00000000000000220000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 517, 522, 1202, 1259, 1601]) (by decide +kernel)

theorem c24494_0 : P.sumLeaves 24 25081856 1021 = 51729310 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24494) (lo := 0) (len := 1021) (W := 51729310) check rows elimOK (by decide) (by decide) cover24494 (by decide)
  decide +kernel

theorem c24494_1 : P.sumLeaves 24 25082877 3 = 3627272 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24494) (lo := 1021) (len := 3) (W := 3627272) check rows elimOK (by decide) (by decide) cover24494 (by decide)
  decide +kernel

theorem h24494 : P.leaf 34 24494 = 55356582 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1021, 51729310), (3, 3627272)]) (.cons c24494_0 (.cons c24494_1 (.nil))) (by decide) (by decide))

theorem cover58751 : P.CoversSplit 24 10 58751 0xfffffffffffaaaaafffffffffffaaaaafffffffffffaaaaafffffffffffaaaaafffcfffcfff8aaa80000000000000000fffcfffcfff8aaa80000000000000000f000f000f000a000f030f030f030a020f000f000f000a000f030f030f020a0200000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [572, 858, 865, 872, 915, 1202, 1308, 1601]) (ps := [(14, [1217], [915])]) (by decide +kernel)

theorem c58751_0 : P.sumLeaves 24 60161024 617 = 47506208 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 58751) (lo := 0) (len := 617) (W := 47506208) check rows elimOK (by decide) (by decide) cover58751 (by decide)
  decide +kernel

theorem c58751_1 : P.sumLeaves 24 60161641 188 = 53012330 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 58751) (lo := 617) (len := 188) (W := 53012330) check rows elimOK (by decide) (by decide) cover58751 (by decide)
  decide +kernel

theorem c58751_2 : P.sumLeaves 24 60161829 116 = 79911660 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 58751) (lo := 805) (len := 116) (W := 79911660) check rows elimOK (by decide) (by decide) cover58751 (by decide)
  decide +kernel

theorem c58751_3 : P.sumLeaves 24 60161945 103 = 137360491 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 58751) (lo := 921) (len := 103) (W := 137360491) check rows elimOK (by decide) (by decide) cover58751 (by decide)
  decide +kernel

theorem h58751 : P.leaf 34 58751 = 317790689 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(617, 47506208), (188, 53012330), (116, 79911660), (103, 137360491)]) (.cons c58751_0 (.cons c58751_1 (.cons c58751_2 (.cons c58751_3 (.nil))))) (by decide) (by decide))

theorem h24495 : P.leaf 34 24495 = 317790689 :=
  orient5 (v := 58751) (by decide) (by decide +kernel) h58751

theorem cover59199 : P.CoversSplit 24 10 59199 0xffffffffffff0000ffffffffffff0000ffffffffcc000000ffffffffcc000000ffffffffffff00000000000000000000ffffffffcc0000000000000000000000ffffffffffff0000ffffffffffff0000ffffffffc8000000ffffffffc8000000a0a0a0a0a0a000000000000000000000a080a080000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 529, 572, 872, 1202, 1217, 1601, 1609]) (ps := [(8, [615], [1272])]) (by decide +kernel)

noncomputable def f59199 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (60619776 + i)

theorem c59199_0 : rowSum f59199 0 442 = 73260297 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59199) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover59199 (by decide)
  decide +kernel

theorem c59199_1 : rowSum f59199 442 486 = 168111746 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59199) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover59199 (by decide)
  decide +kernel

theorem c59199_2 : rowSum f59199 928 96 = 168714387 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59199) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover59199 (by decide)
  decide +kernel

theorem sum59199 : rowSum f59199 0 1024 = 410086430 :=
  rowSum_append (F := f59199) (lo := 0) (n := 442) (m := 582) (A := 73260297) (B := 336826133) c59199_0 (rowSum_append (F := f59199) (lo := 442) (n := 486) (m := 96) (A := 168111746) (B := 168714387) c59199_1 (c59199_2))

theorem h59199 : P.leaf 34 59199 = 410086430 :=
  leaf_weighted (k := 24) (d := 10) (H := 59199) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 59199) (by decide) (by decide +kernel)) sum59199

theorem h24503 : P.leaf 34 24503 = 410086430 :=
  orient5 (v := 59199) (by decide) (by decide +kernel) h59199

theorem cover24535 : P.CoversSplit 24 10 24535 0xfffffffff0f0a0a0fffffffff0f0a0a0fffffffff0f0a0a0fffffffff0f0a0a0cccccccc80008000cc00cc0080008000cccccccc80008000cc00cc0080008000fffffffff0f0a0a0fffffffff0f0a0a0ffffffff00000000ffffffff00000000cccccccc80008000cc00cc008000800000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 916, 1202, 1210, 1259, 1601]) (ps := [(8, [615, 1609], [1266]), (14, [965], [1266])]) (by decide +kernel)

def k24535 : ℕ := 0x8aef000000000000ffff8aef0000000000000000000000000000000000000000ffffffff8aef0000ffffffffffff8aef00000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8aef0000ffffffffffff8aef
def t24535 : ℕ := 0x8ae000000000000ffff08ae0000000000000000000000000000000000000000ffffffff08ae0000ffffffffffff08ae00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff0000000008ae000000000000ffff08ae

noncomputable def f24535 (i : ℕ) := rowWeight k24535 t24535 i * P.leaf 24 (25123840 + i)

theorem c24535_0 : rowSum f24535 0 256 = 3315720 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 24535) (keep := k24535) (twice := t24535) check rows elimOK (by decide) (by decide) cover24535 (by decide)
  decide +kernel

theorem contract24535_1 : P.leaf 30 392564 = 0 := by
  exact leaf_contract_zero (ss := [(8, 0, 1266), (31, 1, 615), (14, 0, 1266), (5, 1, 433), (21, 1, 482), (20, 1, 488), (9, 7, 629), (12, 1, 825), (15, 13, 972)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c24535_1 : rowSum f24535 256 64 = 0 :=
  (rowSum_unit_block (P := P) (keep := k24535) (twice := t24535) (by decide +kernel)).trans ((leaf_eq_inner (k := 24) (d := 6) (H := 392564) rows (by decide) (by decide)).symm.trans contract24535_1)

theorem contract24535_2 : P.leaf 30 392565 = 0 := by
  exact leaf_contract_zero (ss := [(8, 0, 1266), (31, 1, 615), (14, 0, 1266), (5, 1, 433), (21, 1, 482), (20, 1, 488), (9, 7, 629), (12, 1, 825), (15, 13, 972)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c24535_2 : rowSum f24535 320 64 = 0 :=
  (rowSum_unit_block (P := P) (keep := k24535) (twice := t24535) (by decide +kernel)).trans ((leaf_eq_inner (k := 24) (d := 6) (H := 392565) rows (by decide) (by decide)).symm.trans contract24535_2)

theorem c24535_3 : rowSum f24535 384 318 = 134271334 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 24535) (keep := k24535) (twice := t24535) check rows elimOK (by decide) (by decide) cover24535 (by decide)
  decide +kernel

theorem c24535_4 : rowSum f24535 702 322 = 156883150 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 24535) (keep := k24535) (twice := t24535) check rows elimOK (by decide) (by decide) cover24535 (by decide)
  decide +kernel

theorem sum24535 : rowSum f24535 0 1024 = 294470204 :=
  rowSum_append (F := f24535) (lo := 0) (n := 256) (m := 768) (A := 3315720) (B := 291154484) c24535_0 (rowSum_append (F := f24535) (lo := 256) (n := 64) (m := 704) (A := 0) (B := 291154484) c24535_1 (rowSum_append (F := f24535) (lo := 320) (n := 64) (m := 640) (A := 0) (B := 291154484) c24535_2 (rowSum_append (F := f24535) (lo := 384) (n := 318) (m := 322) (A := 134271334) (B := 156883150) c24535_3 (c24535_4))))

theorem h24535 : P.leaf 34 24535 = 294470204 :=
  leaf_weighted (k := 24) (d := 10) (H := 24535) (keep := k24535) (twice := t24535) rows (by decide) (by decide) (balancedRows_of_check (by decide +kernel)) (invRow5 (H := 24535) (by decide) (by decide +kernel)) sum24535

theorem h24507 : P.leaf 34 24507 = 294470204 :=
  orient4 (v := 24535) (by decide) (by decide +kernel) h24535

theorem cover24508 : P.CoversSplit 24 10 24508 0xffaaffaafaaaa0a0ffaaffaafaaaa0a0ffaaffaafaaaa0a0ffaaffaafaaaa0a0cc88cc8888888080cc88cc8888888080cc88cc8888888080cc88cc8888888080ff00ff00fa00a000ff22ff22fa22a020ff00ff00fa00a000ff22ff22fa22a0200000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 916, 1202, 1210, 1308, 1601]) (by decide +kernel)

theorem c24508_0 : P.sumLeaves 24 25096192 490 = 26786567 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24508) (lo := 0) (len := 490) (W := 26786567) check rows elimOK (by decide) (by decide) cover24508 (by decide)
  decide +kernel

theorem c24508_1 : P.sumLeaves 24 25096682 306 = 33937073 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24508) (lo := 490) (len := 306) (W := 33937073) check rows elimOK (by decide) (by decide) cover24508 (by decide)
  decide +kernel

theorem c24508_2 : P.sumLeaves 24 25096988 156 = 62677958 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24508) (lo := 796) (len := 156) (W := 62677958) check rows elimOK (by decide) (by decide) cover24508 (by decide)
  decide +kernel

theorem c24508_3 : P.sumLeaves 24 25097144 72 = 73122696 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24508) (lo := 952) (len := 72) (W := 73122696) check rows elimOK (by decide) (by decide) cover24508 (by decide)
  decide +kernel

theorem h24508 : P.leaf 34 24508 = 196524294 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(490, 26786567), (306, 33937073), (156, 62677958), (72, 73122696)]) (.cons c24508_0 (.cons c24508_1 (.cons c24508_2 (.cons c24508_3 (.nil))))) (by decide) (by decide))

theorem cover24509 : P.CoversSplit 24 10 24509 0xfffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0cccccccc88888080cccccccc88888080cccccccc88888080cccccccc88888080ff00ff00fa00a000ff33ff33fa32a020ff00ff00fa00a000ff33ff33fa22a0200000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 517, 916, 1202, 1210, 1259, 1308, 1601]) (ps := [(14, [1217], [916])]) (by decide +kernel)

theorem c24509_0 : P.sumLeaves 24 25097216 463 = 43970027 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24509) (lo := 0) (len := 463) (W := 43970027) check rows elimOK (by decide) (by decide) cover24509 (by decide)
  decide +kernel

theorem c24509_1 : P.sumLeaves 24 25097679 276 = 53154822 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24509) (lo := 463) (len := 276) (W := 53154822) check rows elimOK (by decide) (by decide) cover24509 (by decide)
  decide +kernel

theorem c24509_2 : P.sumLeaves 24 25097955 142 = 81025459 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24509) (lo := 739) (len := 142) (W := 81025459) check rows elimOK (by decide) (by decide) cover24509 (by decide)
  decide +kernel

theorem c24509_3 : P.sumLeaves 24 25098097 128 = 157096046 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24509) (lo := 881) (len := 128) (W := 157096046) check rows elimOK (by decide) (by decide) cover24509 (by decide)
  decide +kernel

theorem c24509_4 : P.sumLeaves 24 25098225 15 = 37336386 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24509) (lo := 1009) (len := 15) (W := 37336386) check rows elimOK (by decide) (by decide) cover24509 (by decide)
  decide +kernel

theorem h24509 : P.leaf 34 24509 = 372582740 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(463, 43970027), (276, 53154822), (142, 81025459), (128, 157096046), (15, 37336386)]) (.cons c24509_0 (.cons c24509_1 (.cons c24509_2 (.cons c24509_3 (.cons c24509_4 (.nil)))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(24494, 48), (24495, 48), (24503, 12), (24507, 24), (24508, 48), (24509, 48)]

theorem segOK : checkSeg 16 perms 24494 24510 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 24494 24510 228 57216528696 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 57216528696)
    (SegSum.cons (w := 48) h24494 (SegSum.cons (w := 48) h24495 (SegSum.cons (w := 12) h24503 (SegSum.cons (w := 24) h24507 (SegSum.cons (w := 48) h24508 (SegSum.cons (w := 48) h24509 (show SegSum (P.leaf 34) [] 0 from rfl))))))) (by decide)

end RACert.S4N1.C0.S79
