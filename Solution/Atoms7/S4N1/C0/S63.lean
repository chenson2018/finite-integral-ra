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

namespace RACert.S4N1.C0.S63

open RACert RACert.Problem

theorem cover42811 : P.CoversSplit 24 10 42811 0xffffffff00000000ffffffff00000000a0a0000000000000a0a00000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc0000000000000000000000000080008c0000000000a0200000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [474, 486, 517, 572, 860, 915, 1202, 1209, 1258, 1601]) (ps := [(16, [528, 871, 1251], [1258])]) (by decide +kernel)

noncomputable def f42811 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (43838464 + i)

theorem c42811_0 : rowSum f42811 0 1024 = 13355224 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 42811) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover42811 (by decide)
  decide +kernel

theorem sum42811 : rowSum f42811 0 1024 = 13355224 :=
  c42811_0

theorem h42811 : P.leaf 34 42811 = 13355224 :=
  leaf_weighted (k := 24) (d := 10) (H := 42811) (keep := keep5) (twice := twice5) rows (by decide) (by decide) (bal5) (invRow5 (H := 42811) (by decide) (by decide +kernel)) sum42811

theorem h22199 : P.leaf 34 22199 = 13355224 :=
  orient5 (v := 42811) (by decide) (by decide +kernel) h42811

theorem cover22204 : P.CoversSplit 24 10 22204 0xfca9fca9f8a80000fca9fca9f8a80000fca9fca900000000fca90000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c80000000000000000000000cc21cc21c800000000210000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 524, 566, 573, 909, 916, 1202, 1210, 1217, 1251, 1259, 1601]) (ps := [(8, [580], [573])]) (by decide +kernel)

noncomputable def f22204 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (22736896 + i)

theorem c22204_0 : rowSum f22204 0 1024 = 5886876 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 22204) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover22204 (by decide)
  decide +kernel

theorem sum22204 : rowSum f22204 0 1024 = 5886876 :=
  c22204_0

theorem h22204 : P.leaf 34 22204 = 5886876 :=
  leaf_weighted (k := 24) (d := 10) (H := 22204) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 22204) (by decide) (by decide +kernel)) sum22204

theorem cover22205 : P.CoversSplit 24 10 22205 0xfffffffffafa0000fffffffffafa0000ffffffff00000000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c80000000000000000000000cc33cc33c800000000330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 517, 524, 566, 573, 909, 916, 1202, 1210, 1217, 1251, 1259, 1601]) (ps := [(8, [580], [573])]) (by decide +kernel)

noncomputable def f22205 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (22737920 + i)

theorem c22205_0 : rowSum f22205 0 1002 = 13036534 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 22205) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover22205 (by decide)
  decide +kernel

theorem c22205_1 : rowSum f22205 1002 22 = 5139554 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 22205) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover22205 (by decide)
  decide +kernel

theorem sum22205 : rowSum f22205 0 1024 = 18176088 :=
  rowSum_append (F := f22205) (lo := 0) (n := 1002) (m := 22) (A := 13036534) (B := 5139554) c22205_0 (c22205_1)

theorem h22205 : P.leaf 34 22205 = 18176088 :=
  leaf_weighted (k := 24) (d := 10) (H := 22205) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 22205) (by decide) (by decide +kernel)) sum22205

theorem cover60231 : P.CoversSplit 24 10 60231 0xfffffffff0f00000fffffffff0f000008c8c8c8c000000008c8c8c8c00000000ff00ff00f000000000000000000000008c008c0000000000000000000000000088aa88aa80a0000088aa88aa80a00000888888880000000088888888000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 516, 522, 523, 565, 572, 859, 915, 1202, 1601]) (by decide +kernel)

noncomputable def f60231 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (61676544 + i)

theorem c60231_0 : rowSum f60231 0 1024 = 16396194 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 60231) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover60231 (by decide)
  decide +kernel

theorem sum60231 : rowSum f60231 0 1024 = 16396194 :=
  c60231_0

theorem h60231 : P.leaf 34 60231 = 16396194 :=
  leaf_weighted (k := 24) (d := 10) (H := 60231) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 60231) (by decide) (by decide +kernel)) sum60231

theorem h22206 : P.leaf 34 22206 = 16396194 :=
  orient32 (v := 60231) (by decide) (by decide +kernel) h60231

theorem cover22207 : P.CoversSplit 24 10 22207 0xfffffffffafa0000fffffffffafa0000ffffffff00000000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c80000000000000000000000cc33cc33c800000000330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 524, 566, 573, 909, 916, 1202, 1210, 1217, 1251, 1259, 1601]) (ps := [(8, [580], [573])]) (by decide +kernel)

noncomputable def f22207 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (22739968 + i)

theorem c22207_0 : rowSum f22207 0 1002 = 34295486 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 22207) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover22207 (by decide)
  decide +kernel

theorem c22207_1 : rowSum f22207 1002 22 = 12059652 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 22207) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover22207 (by decide)
  decide +kernel

theorem sum22207 : rowSum f22207 0 1024 = 46355138 :=
  rowSum_append (F := f22207) (lo := 0) (n := 1002) (m := 22) (A := 34295486) (B := 12059652) c22207_0 (c22207_1)

theorem h22207 : P.leaf 34 22207 = 46355138 :=
  leaf_weighted (k := 24) (d := 10) (H := 22207) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 22207) (by decide) (by decide +kernel)) sum22207

theorem cover22230 : P.CoversSplit 24 10 22230 0xfffffffff0f00000fffffffff0f00000aaaaaaaa00000000aaaaaaaa000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c00000000000000000000000800080000000000000200020000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 475, 516, 573, 860, 916, 1202, 1210, 1259, 1601]) (ps := [(8, [468], [516, 573, 1266])]) (by decide +kernel)

theorem c22230_0 : P.sumLeaves 24 22763520 994 = 4972509 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22230) (lo := 0) (len := 994) (W := 4972509) check rows elimOK (by decide) (by decide) cover22230 (by decide)
  decide +kernel

theorem c22230_1 : P.sumLeaves 24 22764514 30 = 3464712 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22230) (lo := 994) (len := 30) (W := 3464712) check rows elimOK (by decide) (by decide) cover22230 (by decide)
  decide +kernel

theorem h22230 : P.leaf 34 22230 = 8437221 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(994, 4972509), (30, 3464712)]) (.cons c22230_0 (.cons c22230_1 (.nil))) (by decide) (by decide))

theorem cover22231 : P.CoversSplit 24 10 22231 0xfffffffff0f00000fffffffff0f00000ffffffff00000000ffffffff000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c00000000000000000000000cc00cc000000000000330033000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [475, 516, 573, 860, 916, 1202, 1210, 1217, 1259, 1601]) (ps := [(8, [615], [573, 1217, 1266])]) (by decide +kernel)

theorem c22231_0 : P.sumLeaves 24 22764544 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22231) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover22231 (by decide)
  decide +kernel

theorem contract22231_1 : P.leaf 30 355700 = 0 := by
  exact leaf_contract_zero (ss := [(17, 0, 1259), (31, 1, 615), (12, 1, 958), (29, 0, 1259), (14, 0, 916), (15, 0, 916), (5, 1, 608), (27, 0, 916), (8, 0, 573), (21, 1, 482), (20, 1, 488), (9, 0, 573), (18, 1, 578)]) (q := 580) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c22231_1 : P.sumLeaves 24 22764800 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 355700) rows (by decide) (by decide)).symm.trans contract22231_1

theorem contract22231_2 : P.leaf 30 355701 = 0 := by
  exact leaf_contract_zero (ss := [(27, 1, 573), (29, 1, 916), (8, 0, 1266), (14, 0, 580), (21, 1, 482)]) (q := 580) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c22231_2 : P.sumLeaves 24 22764864 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 355701) rows (by decide) (by decide)).symm.trans contract22231_2

theorem c22231_3 : P.sumLeaves 24 22764928 558 = 14114921 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22231) (lo := 384) (len := 558) (W := 14114921) check rows elimOK (by decide) (by decide) cover22231 (by decide)
  decide +kernel

theorem c22231_4 : P.sumLeaves 24 22765486 82 = 22223384 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22231) (lo := 942) (len := 82) (W := 22223384) check rows elimOK (by decide) (by decide) cover22231 (by decide)
  decide +kernel

theorem h22231 : P.leaf 34 22231 = 36338305 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 0), (64, 0), (558, 14114921), (82, 22223384)]) (.cons c22231_0 (.cons c22231_1 (.cons c22231_2 (.cons c22231_3 (.cons c22231_4 (.nil)))))) (by decide) (by decide))

theorem cover22236 : P.CoversSplit 24 10 22236 0xfca8fca8f0a00000fca8fca8f0a00000a8a8aca800000000a8a8aca8000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c0000000000000000000000088008c000000000000200020000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 472, 473, 508, 516, 536, 573, 867, 916, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c22236_0 : P.sumLeaves 24 22769664 320 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22236) (lo := 0) (len := 320) (W := 0) check rows elimOK (by decide) (by decide) cover22236 (by decide)
  decide +kernel

theorem contract22236_1 : P.leaf 30 355781 = 0 := by
  exact leaf_contract_zero (ss := [(18, 1, 475), (31, 1, 536), (27, 1, 573), (29, 1, 916), (8, 0, 1266), (20, 1, 531), (21, 1, 537)]) (q := 580) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c22236_1 : P.sumLeaves 24 22769984 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 355781) rows (by decide) (by decide)).symm.trans contract22236_1

theorem c22236_2 : P.sumLeaves 24 22770048 640 = 9834125 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22236) (lo := 384) (len := 640) (W := 9834125) check rows elimOK (by decide) (by decide) cover22236 (by decide)
  decide +kernel

theorem h22236 : P.leaf 34 22236 = 9834125 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(320, 0), (64, 0), (640, 9834125)]) (.cons c22236_0 (.cons c22236_1 (.cons c22236_2 (.nil)))) (by decide) (by decide))

theorem cover23275 : P.CoversSplit 24 10 23275 0xffffffffaaaa0000ffffffffaaaa0000ffff00000000aaaaffff00000000aaaa0000000000000000000000000000000000000000000000000000000000000000cc00cc00880000000000000000000000cc0000000000000000330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 573, 879, 916, 1202, 1210, 1259, 1601]) (ps := [(8, [1217], [573]), (14, [958], [916, 1266]), (17, [1251], [1259]), (18, [524], [1210])]) (by decide +kernel)

theorem c23275_0 : P.sumLeaves 24 23833600 950 = 8974537 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23275) (lo := 0) (len := 950) (W := 8974537) check rows elimOK (by decide) (by decide) cover23275 (by decide)
  decide +kernel

theorem c23275_1 : P.sumLeaves 24 23834550 74 = 17858490 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23275) (lo := 950) (len := 74) (W := 17858490) check rows elimOK (by decide) (by decide) cover23275 (by decide)
  decide +kernel

theorem h23275 : P.leaf 34 23275 = 26833027 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(950, 8974537), (74, 17858490)]) (.cons c23275_0 (.cons c23275_1 (.nil))) (by decide) (by decide))

theorem h22237 : P.leaf 34 22237 = 26833027 :=
  orient4 (v := 23275) (by decide) (by decide +kernel) h23275

theorem cover22238 : P.CoversSplit 24 10 22238 0xfffffffff0f00000fffffffff0f00000aaaaafaf00000000aaaaafaf000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c0000000000000000000000088008c000000000000220022000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 516, 536, 573, 860, 916, 1202, 1210, 1259, 1601]) (ps := [(17, [528], [1259])]) (by decide +kernel)

theorem c22238_0 : P.sumLeaves 24 22771712 320 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22238) (lo := 0) (len := 320) (W := 0) check rows elimOK (by decide) (by decide) cover22238 (by decide)
  decide +kernel

theorem contract22238_1 : P.leaf 30 355813 = 0 := by
  exact leaf_contract_zero (ss := [(27, 1, 573), (29, 1, 916), (8, 0, 1266), (21, 1, 537)]) (q := 580) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c22238_1 : P.sumLeaves 24 22772032 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 355813) rows (by decide) (by decide)).symm.trans contract22238_1

theorem c22238_2 : P.sumLeaves 24 22772096 606 = 14212035 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22238) (lo := 384) (len := 606) (W := 14212035) check rows elimOK (by decide) (by decide) cover22238 (by decide)
  decide +kernel

theorem c22238_3 : P.sumLeaves 24 22772702 34 = 9130161 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22238) (lo := 990) (len := 34) (W := 9130161) check rows elimOK (by decide) (by decide) cover22238 (by decide)
  decide +kernel

theorem h22238 : P.leaf 34 22238 = 23342196 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(320, 0), (64, 0), (606, 14212035), (34, 9130161)]) (.cons c22238_0 (.cons c22238_1 (.cons c22238_2 (.cons c22238_3 (.nil))))) (by decide) (by decide))

theorem cover22239 : P.CoversSplit 24 10 22239 0xfffffffff0f00000fffffffff0f00000ffffffff00000000ffffffff000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c00000000000000000000000cc00cc00c000000000330033003000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [516, 536, 573, 860, 916, 1202, 1210, 1217, 1259, 1601]) (by decide +kernel)

theorem c22239_0 : P.sumLeaves 24 22772736 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22239) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover22239 (by decide)
  decide +kernel

theorem contract22239_1 : P.leaf 30 355828 = 0 := by
  exact leaf_contract_zero (ss := [(17, 0, 1259), (12, 1, 958), (29, 0, 1259), (14, 0, 916), (15, 0, 916), (27, 0, 916), (8, 0, 573), (5, 1, 433), (20, 1, 531), (21, 1, 537), (9, 0, 573), (18, 1, 578)]) (q := 580) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c22239_1 : P.sumLeaves 24 22772992 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 355828) rows (by decide) (by decide)).symm.trans contract22239_1

theorem contract22239_2 : P.leaf 30 355829 = 0 := by
  exact leaf_contract_zero (ss := [(27, 1, 573), (29, 1, 916), (8, 0, 1266), (14, 0, 580), (5, 1, 433), (20, 1, 531), (21, 1, 537)]) (q := 580) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c22239_2 : P.sumLeaves 24 22773056 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 355829) rows (by decide) (by decide)).symm.trans contract22239_2

theorem c22239_3 : P.sumLeaves 24 22773120 558 = 26196677 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22239) (lo := 384) (len := 558) (W := 26196677) check rows elimOK (by decide) (by decide) cover22239 (by decide)
  decide +kernel

theorem c22239_4 : P.sumLeaves 24 22773678 82 = 37440464 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22239) (lo := 942) (len := 82) (W := 37440464) check rows elimOK (by decide) (by decide) cover22239 (by decide)
  decide +kernel

theorem h22239 : P.leaf 34 22239 = 63637141 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 0), (64, 0), (558, 26196677), (82, 37440464)]) (.cons c22239_0 (.cons c22239_1 (.cons c22239_2 (.cons c22239_3 (.cons c22239_4 (.nil)))))) (by decide) (by decide))

theorem cover23260 : P.CoversSplit 24 10 23260 0xfca8fca800000000fca8fca800000000a0a0000000000000a0a00000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 466, 472, 473, 516, 536, 573, 859, 916, 1202, 1210, 1259, 1601]) (ps := [(17, [467], [1259]), (18, [475], [1210])]) (by decide +kernel)

noncomputable def f23260 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (23818240 + i)

theorem c23260_0 : rowSum f23260 0 1024 = 8115944 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 23260) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover23260 (by decide)
  decide +kernel

theorem sum23260 : rowSum f23260 0 1024 = 8115944 :=
  c23260_0

theorem h23260 : P.leaf 34 23260 = 8115944 :=
  leaf_weighted (k := 24) (d := 10) (H := 23260) (keep := keep5) (twice := twice5) rows (by decide) (by decide) (bal5) (invRow5 (H := 23260) (by decide) (by decide +kernel)) sum23260

theorem h22250 : P.leaf 34 22250 = 8115944 :=
  orient4 (v := 23260) (by decide) (by decide +kernel) h23260

theorem cover23261 : P.CoversSplit 24 10 23261 0xffffffff00000000ffffffff00000000a0a0000000000000a0a00000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00000000000000000000000000800000000000000080200000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 516, 536, 573, 859, 916, 1202, 1210, 1259, 1601]) (ps := [(17, [528, 1251], [1259]), (18, [475], [1210])]) (by decide +kernel)

noncomputable def f23261 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (23819264 + i)

theorem c23261_0 : rowSum f23261 0 1024 = 14174951 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 23261) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover23261 (by decide)
  decide +kernel

theorem sum23261 : rowSum f23261 0 1024 = 14174951 :=
  c23261_0

theorem h23261 : P.leaf 34 23261 = 14174951 :=
  leaf_weighted (k := 24) (d := 10) (H := 23261) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 23261) (by decide) (by decide +kernel)) sum23261

theorem h22251 : P.leaf 34 22251 = 14174951 :=
  orient4 (v := 23261) (by decide) (by decide +kernel) h23261

theorem cover23276 : P.CoversSplit 24 10 23276 0xcccccccc88880000cccccccc88880000c0c0000000000000c0c00000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00880000000000000000000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 466, 515, 573, 859, 879, 916, 1202, 1210, 1259, 1601]) (ps := [(18, [475], [1210])]) (by decide +kernel)

theorem c23276_0 : P.sumLeaves 24 23834624 1024 = 8003683 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23276) (lo := 0) (len := 1024) (W := 8003683) check rows elimOK (by decide) (by decide) cover23276 (by decide)
  decide +kernel

theorem h23276 : P.leaf 34 23276 = 8003683 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8003683)]) (.cons c23276_0 (.nil)) (by decide) (by decide))

theorem h22252 : P.leaf 34 22252 = 8003683 :=
  orient4 (v := 23276) (by decide) (by decide +kernel) h23276

theorem cover23277 : P.CoversSplit 24 10 23277 0xffffffffaaaa0000ffffffffaaaa0000ffff000000000000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00880000000000000000000000cc0000000000000000330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 522, 573, 879, 916, 1202, 1210, 1259, 1601]) (ps := [(17, [1251], [1259]), (18, [475], [1210])]) (by decide +kernel)

theorem c23277_0 : P.sumLeaves 24 23835648 989 = 12459152 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23277) (lo := 0) (len := 989) (W := 12459152) check rows elimOK (by decide) (by decide) cover23277 (by decide)
  decide +kernel

theorem c23277_1 : P.sumLeaves 24 23836637 35 = 8888444 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23277) (lo := 989) (len := 35) (W := 8888444) check rows elimOK (by decide) (by decide) cover23277 (by decide)
  decide +kernel

theorem h23277 : P.leaf 34 23277 = 21347596 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(989, 12459152), (35, 8888444)]) (.cons c23277_0 (.cons c23277_1 (.nil))) (by decide) (by decide))

theorem h22253 : P.leaf 34 22253 = 21347596 :=
  orient4 (v := 23277) (by decide) (by decide +kernel) h23277

def seg : List (ℕ × ℕ) := [(22199, 24), (22204, 24), (22205, 24), (22206, 24), (22207, 24), (22230, 16), (22231, 16), (22236, 48), (22237, 48), (22238, 48), (22239, 48), (22250, 12), (22251, 24), (22252, 48), (22253, 48)]

theorem segOK : checkSeg 16 perms 22199 22254 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 22199 22254 476 10901959912 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 10901959912)
    (SegSum.cons (w := 24) h22199 (SegSum.cons (w := 24) h22204 (SegSum.cons (w := 24) h22205 (SegSum.cons (w := 24) h22206 (SegSum.cons (w := 24) h22207 (SegSum.cons (w := 16) h22230 (SegSum.cons (w := 16) h22231 (SegSum.cons (w := 48) h22236 (SegSum.cons (w := 48) h22237 (SegSum.cons (w := 48) h22238 (SegSum.cons (w := 48) h22239 (SegSum.cons (w := 12) h22250 (SegSum.cons (w := 24) h22251 (SegSum.cons (w := 48) h22252 (SegSum.cons (w := 48) h22253 (show SegSum (P.leaf 34) [] 0 from rfl)))))))))))))))) (by decide)

end RACert.S4N1.C0.S63
