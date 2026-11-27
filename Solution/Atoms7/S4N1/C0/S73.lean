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

namespace RACert.S4N1.C0.S73

open RACert RACert.Problem

theorem cover22199 : P.CoversSplit 24 10 22199 0xffffffffaaaa0000ffffffffaaaa0000ffffffff00000000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00880000000000000000000000ff33ff338800000000330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 573, 867, 909, 916, 1202, 1210, 1217, 1251, 1259, 1601]) (ps := [(5, [517], [566]), (8, [580], [573])]) (by decide +kernel)

theorem c22199_0 : P.sumLeaves 24 22731776 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22199) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover22199 (by decide)
  decide +kernel

theorem contract22199_1 : P.leaf 30 355188 = 144 := by
  exact leaf_contract_factors (k := 30) (b := 8) (H := 355188) (ss := [(30, 1, 1251), (31, 1, 1251), (17, 0, 1259), (5, 1, 615), (27, 0, 1259), (8, 0, 573), (14, 0, 531), (21, 0, 482), (20, 1, 433), (9, 0, 573), (2, 1, 453), (22, 1, 404), (6, 1, 461), (3, 1, 502), (26, 1, 517), (4, 1, 551), (18, 1, 578), (7, 1, 628), (13, 1, 971), (29, 0, 1259), (15, 0, 916), (16, 1, 1314)]) (ids := [8, 9, 10, 17, 23, 21, 22, 26]) (cs := [1, 1, 1, 1, 1, 1, 0, 0, 2, 3, 4, 1, 0, 0, 1, 0, 1, 5, 1, 0, 1, 7, 8, 6, 1, 0, 9, 0, 1, 1]) (bs := [3, 2, 3]) (W := 144) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c22199_1 : P.sumLeaves 24 22732032 64 = 144 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 355188) rows (by decide) (by decide)).symm.trans contract22199_1

theorem c22199_2 : P.sumLeaves 24 22732096 612 = 3502200 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22199) (lo := 320) (len := 612) (W := 3502200) check rows elimOK (by decide) (by decide) cover22199 (by decide)
  decide +kernel

theorem c22199_3 : P.sumLeaves 24 22732708 92 = 9852880 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22199) (lo := 932) (len := 92) (W := 9852880) check rows elimOK (by decide) (by decide) cover22199 (by decide)
  decide +kernel

theorem h22199 : P.leaf 34 22199 = 13355224 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 144), (612, 3502200), (92, 9852880)]) (.cons c22199_0 (.cons c22199_1 (.cons c22199_2 (.cons c22199_3 (.nil))))) (by decide) (by decide))

theorem cover22204 : P.CoversSplit 24 10 22204 0xfca9fca9f8a80000fca9fca9f8a80000fca9fca900000000fca90000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c80000000000000000000000cc21cc21c800000000210000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 524, 566, 573, 909, 916, 1202, 1210, 1217, 1251, 1259, 1601]) (ps := [(8, [580], [573])]) (by decide +kernel)

noncomputable def f22204 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (22736896 + i)

theorem c22204_0 : rowSum f22204 0 1024 = 5886876 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 22204) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover22204 (by decide)
  decide +kernel

theorem sum22204 : rowSum f22204 0 1024 = 5886876 :=
  c22204_0

theorem h22204 : P.leaf 34 22204 = 5886876 :=
  leaf_weighted (k := 24) (d := 10) (H := 22204) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 22204) (by decide) (by decide +kernel)) sum22204

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
  leaf_weighted (k := 24) (d := 10) (H := 22205) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 22205) (by decide) (by decide +kernel)) sum22205

theorem cover22206 : P.CoversSplit 24 10 22206 0xfffffffffafa0000fffffffffafa0000ffffffff00000000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c80000000000000000000000cc33cc33c800000000330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 517, 524, 566, 573, 909, 916, 1202, 1210, 1217, 1251, 1259, 1601]) (ps := [(8, [580], [573])]) (by decide +kernel)

noncomputable def f22206 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (22738944 + i)

theorem c22206_0 : rowSum f22206 0 1002 = 11738090 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 22206) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover22206 (by decide)
  decide +kernel

theorem c22206_1 : rowSum f22206 1002 22 = 4658104 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 22206) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover22206 (by decide)
  decide +kernel

theorem sum22206 : rowSum f22206 0 1024 = 16396194 :=
  rowSum_append (F := f22206) (lo := 0) (n := 1002) (m := 22) (A := 11738090) (B := 4658104) c22206_0 (c22206_1)

theorem h22206 : P.leaf 34 22206 = 16396194 :=
  leaf_weighted (k := 24) (d := 10) (H := 22206) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 22206) (by decide) (by decide +kernel)) sum22206

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
  leaf_weighted (k := 24) (d := 10) (H := 22207) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 22207) (by decide) (by decide +kernel)) sum22207

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

theorem cover22237 : P.CoversSplit 24 10 22237 0xfffffffff0f00000fffffffff0f00000ffffffff00000000ffffffff000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c00000000000000000000000cc00cc000000000000330033000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 516, 536, 573, 860, 867, 916, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c22237_0 : P.sumLeaves 24 22770688 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22237) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover22237 (by decide)
  decide +kernel

theorem contract22237_1 : P.leaf 30 355796 = 0 := by
  exact leaf_contract_zero (ss := [(18, 1, 475), (31, 1, 536), (17, 0, 1259), (12, 1, 958), (29, 0, 1259), (14, 0, 916), (4, 1, 487), (11, 1, 818), (15, 0, 916), (27, 0, 916), (8, 0, 573), (5, 1, 433), (20, 1, 531), (21, 1, 537), (9, 0, 573)]) (q := 580) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c22237_1 : P.sumLeaves 24 22770944 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 355796) rows (by decide) (by decide)).symm.trans contract22237_1

theorem contract22237_2 : P.leaf 30 355797 = 0 := by
  exact leaf_contract_zero (ss := [(18, 1, 475), (31, 1, 536), (27, 1, 573), (29, 1, 916), (8, 0, 1266), (21, 0, 580), (14, 1, 537), (20, 1, 586), (10, 1, 874), (11, 1, 923)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c22237_2 : P.sumLeaves 24 22771008 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 355797) rows (by decide) (by decide)).symm.trans contract22237_2

theorem c22237_3 : P.sumLeaves 24 22771072 558 = 11100655 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22237) (lo := 384) (len := 558) (W := 11100655) check rows elimOK (by decide) (by decide) cover22237 (by decide)
  decide +kernel

theorem c22237_4 : P.sumLeaves 24 22771630 82 = 15732372 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22237) (lo := 942) (len := 82) (W := 15732372) check rows elimOK (by decide) (by decide) cover22237 (by decide)
  decide +kernel

theorem h22237 : P.leaf 34 22237 = 26833027 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 0), (64, 0), (558, 11100655), (82, 15732372)]) (.cons c22237_0 (.cons c22237_1 (.cons c22237_2 (.cons c22237_3 (.cons c22237_4 (.nil)))))) (by decide) (by decide))

theorem cover22238 : P.CoversSplit 24 10 22238 0xfffffffff0f00000fffffffff0f00000aaaaafaf00000000aaaaafaf000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c0000000000000000000000088008c000000000000220022000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 516, 536, 573, 860, 916, 1202, 1210, 1259, 1601]) (ps := [(17, [528], [1259])]) (by decide +kernel)

theorem c22238_0 : P.sumLeaves 24 22771712 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22238) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover22238 (by decide)
  decide +kernel

theorem contract22238_1 : P.leaf 30 355812 = 0 := by
  exact leaf_contract_zero (ss := [(17, 0, 1259), (6, 1, 467), (26, 1, 528), (31, 1, 528), (12, 1, 958), (29, 0, 1259), (14, 0, 916), (3, 1, 509), (10, 1, 811), (21, 1, 874), (8, 1, 580), (27, 1, 573), (18, 1, 580), (20, 1, 880)]) (q := 916) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c22238_1 : P.sumLeaves 24 22771968 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 355812) rows (by decide) (by decide)).symm.trans contract22238_1

theorem contract22238_2 : P.leaf 30 355813 = 0 := by
  exact leaf_contract_zero (ss := [(27, 1, 573), (29, 1, 916), (8, 0, 1266), (21, 1, 537)]) (q := 580) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c22238_2 : P.sumLeaves 24 22772032 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 355813) rows (by decide) (by decide)).symm.trans contract22238_2

theorem c22238_3 : P.sumLeaves 24 22772096 606 = 14212035 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22238) (lo := 384) (len := 606) (W := 14212035) check rows elimOK (by decide) (by decide) cover22238 (by decide)
  decide +kernel

theorem c22238_4 : P.sumLeaves 24 22772702 34 = 9130161 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22238) (lo := 990) (len := 34) (W := 9130161) check rows elimOK (by decide) (by decide) cover22238 (by decide)
  decide +kernel

theorem h22238 : P.leaf 34 22238 = 23342196 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 0), (64, 0), (606, 14212035), (34, 9130161)]) (.cons c22238_0 (.cons c22238_1 (.cons c22238_2 (.cons c22238_3 (.cons c22238_4 (.nil)))))) (by decide) (by decide))

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

theorem cover22250 : P.CoversSplit 24 10 22250 0xfffffffff0f00000fffffffff0f00000fffffffff0f00000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c00000000000000000000000cccccccc8080000000330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 522, 573, 860, 916, 1202, 1210, 1251, 1259, 1601]) (ps := [(14, [923, 1217], [916, 1266])]) (by decide +kernel)

theorem c22250_0 : P.sumLeaves 24 22784000 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22250) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover22250 (by decide)
  decide +kernel

theorem contract22250_1 : P.leaf 30 356004 = 0 := by
  exact leaf_contract_zero (ss := [(6, 1, 472), (18, 1, 524), (12, 1, 803), (30, 1, 1251), (31, 1, 1251), (17, 0, 1259), (27, 0, 1259), (10, 1, 508), (4, 1, 566), (8, 0, 573), (5, 1, 551), (9, 0, 573), (20, 1, 538), (29, 0, 573), (14, 0, 580), (15, 1, 486), (21, 0, 488), (7, 1, 628)]) (q := 678) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c22250_1 : P.sumLeaves 24 22784256 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 356004) rows (by decide) (by decide)).symm.trans contract22250_1

theorem contract22250_2 : P.leaf 30 356005 = 1024 := by
  exact leaf_contract_factors (k := 30) (b := 10) (H := 356005) (ss := [(18, 1, 524), (27, 1, 573), (14, 0, 1266), (15, 1, 486), (12, 1, 487), (11, 1, 818), (6, 1, 460), (10, 1, 811), (21, 0, 874), (20, 1, 880), (29, 1, 916), (8, 0, 923), (5, 1, 433), (7, 1, 628), (9, 1, 678), (13, 1, 971), (31, 1, 1217), (16, 1, 1314), (17, 1, 1364), (19, 1, 1707)]) (ids := [0, 1, 2, 20, 21, 22, 23, 24, 26, 28]) (cs := [2, 3, 4, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 5, 6, 7, 8, 9, 1, 10, 1, 11, 1]) (bs := [0, 10]) (W := 1024) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c22250_2 : P.sumLeaves 24 22784320 64 = 1024 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 356005) rows (by decide) (by decide)).symm.trans contract22250_2

theorem c22250_3 : P.sumLeaves 24 22784384 566 = 2656462 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22250) (lo := 384) (len := 566) (W := 2656462) check rows elimOK (by decide) (by decide) cover22250 (by decide)
  decide +kernel

theorem c22250_4 : P.sumLeaves 24 22784950 74 = 5458458 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22250) (lo := 950) (len := 74) (W := 5458458) check rows elimOK (by decide) (by decide) cover22250 (by decide)
  decide +kernel

theorem h22250 : P.leaf 34 22250 = 8115944 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 0), (64, 1024), (566, 2656462), (74, 5458458)]) (.cons c22250_0 (.cons c22250_1 (.cons c22250_2 (.cons c22250_3 (.cons c22250_4 (.nil)))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(22199, 24), (22204, 24), (22205, 24), (22206, 24), (22207, 24), (22230, 16), (22231, 16), (22236, 48), (22237, 48), (22238, 48), (22239, 48), (22250, 12)]

theorem segOK : checkSeg 16 perms 22199 22251 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 22199 22251 356 9152899696 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 9152899696)
    (SegSum.cons (w := 24) h22199 (SegSum.cons (w := 24) h22204 (SegSum.cons (w := 24) h22205 (SegSum.cons (w := 24) h22206 (SegSum.cons (w := 24) h22207 (SegSum.cons (w := 16) h22230 (SegSum.cons (w := 16) h22231 (SegSum.cons (w := 48) h22236 (SegSum.cons (w := 48) h22237 (SegSum.cons (w := 48) h22238 (SegSum.cons (w := 48) h22239 (SegSum.cons (w := 12) h22250 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))) (by decide)

end RACert.S4N1.C0.S73
