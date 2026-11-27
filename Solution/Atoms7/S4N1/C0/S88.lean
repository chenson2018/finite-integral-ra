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

namespace RACert.S4N1.C0.S88

open RACert RACert.Problem

theorem cover24015 : P.CoversSplit 24 10 24015 0xfffffffff0f0a0a0fffffffff0f0a0a0ffff000000005050ffff000000005000cccccccc80008000cc00cc0080008000cccc000040004000cc00000040004000fffffffff0f0a0a00000000000000000ffff55550000505000ff005500000050000000000080008000cc008800800080000000000040004000cc004400400040 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 858, 865, 1202, 1210, 1259, 1601]) (ps := [(17, [1259], [1251]), (18, [1210], [1264])]) (by decide +kernel)

noncomputable def f24015 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (24591360 + i)

theorem c24015_0 : rowSum f24015 0 739 = 24414652 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 24015) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover24015 (by decide)
  decide +kernel

theorem c24015_1 : rowSum f24015 739 285 = 40291821 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 24015) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover24015 (by decide)
  decide +kernel

theorem sum24015 : rowSum f24015 0 1024 = 64706473 :=
  rowSum_append (F := f24015) (lo := 0) (n := 739) (m := 285) (A := 24414652) (B := 40291821) c24015_0 (c24015_1)

theorem h24015 : P.leaf 34 24015 = 64706473 :=
  leaf_weighted (k := 24) (d := 10) (H := 24015) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 24015) (by decide) (by decide +kernel)) sum24015

theorem cover24026 : P.CoversSplit 24 10 24026 0xfffffffff0f0a0a0fffffffff0f0a0a0aaaa000000005050aaaa000000005050ccc0ccc080008000cc00cc008000800088800000000040008800000000004000fffffffff0f0a0a0fffffffff0f0a0a0aaaa555500005050aaaa555500005050ccc0ccc080008000cc00cc008000800088004400000040008800440000004000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 516, 858, 865, 1202, 1210, 1259, 1601]) (ps := [(8, [1609], [516, 1266])]) (by decide +kernel)

theorem contract24026_0 : P.leaf 30 384416 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 487), (3, 1, 536), (10, 1, 865), (29, 1, 865), (18, 11, 879), (12, 1, 916), (8, 0, 1266), (7, 6, 467), (20, 1, 531), (21, 0, 537), (5, 1, 565), (14, 0, 629), (26, 6, 509), (30, 11, 867), (31, 1, 1217), (27, 1, 1601)]) (q := 1609) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c24026_0 : P.sumLeaves 24 24602624 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 384416) rows (by decide) (by decide)).symm.trans contract24026_0

theorem contract24026_1 : P.leaf 30 384417 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 487), (3, 1, 536), (18, 11, 879), (8, 0, 1266), (7, 6, 467), (20, 1, 531), (21, 0, 537), (5, 1, 580), (14, 0, 629), (26, 6, 509), (12, 1, 825), (30, 11, 867), (31, 1, 1217), (27, 1, 1601)]) (q := 1609) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c24026_1 : P.sumLeaves 24 24602688 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 384417) rows (by decide) (by decide)).symm.trans contract24026_1

theorem c24026_2 : P.sumLeaves 24 24602752 308 = 1735142 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24026) (lo := 128) (len := 308) (W := 1735142) check rows elimOK (by decide) (by decide) cover24026 (by decide)
  decide +kernel

theorem c24026_3 : P.sumLeaves 24 24603060 391 = 6790269 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24026) (lo := 436) (len := 391) (W := 6790269) check rows elimOK (by decide) (by decide) cover24026 (by decide)
  decide +kernel

theorem c24026_4 : P.sumLeaves 24 24603451 190 = 14554946 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24026) (lo := 827) (len := 190) (W := 14554946) check rows elimOK (by decide) (by decide) cover24026 (by decide)
  decide +kernel

theorem c24026_5 : P.sumLeaves 24 24603641 7 = 3116832 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24026) (lo := 1017) (len := 7) (W := 3116832) check rows elimOK (by decide) (by decide) cover24026 (by decide)
  decide +kernel

theorem h24026 : P.leaf 34 24026 = 26197189 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 0), (64, 0), (308, 1735142), (391, 6790269), (190, 14554946), (7, 3116832)]) (.cons c24026_0 (.cons c24026_1 (.cons c24026_2 (.cons c24026_3 (.cons c24026_4 (.cons c24026_5 (.nil))))))) (by decide) (by decide))

theorem cover24027 : P.CoversSplit 24 10 24027 0xfffffffff0f0a0a0fffffffff0f0a0a0ffff000000000000ffff000000000000cccccccc80008000cc00cc0080008000cccc000040000000cc00000040000000fffffffff0f0a0a0fffffffff0f0a0a0ffff555500000000ffff555500000000cccccccc80008000cc00cc0080008000cc00440040000000cc00440040000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 858, 865, 916, 1202, 1210, 1259, 1601]) (ps := [(8, [1609], [1266])]) (by decide +kernel)

theorem contract24027_0 : P.leaf 30 384432 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 487), (3, 1, 536), (11, 1, 879), (12, 1, 916), (29, 1, 916), (8, 0, 1266), (14, 0, 537), (5, 1, 433), (20, 1, 482), (21, 0, 488), (30, 1, 867), (31, 1, 1217), (27, 1, 1601)]) (q := 1609) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c24027_0 : P.sumLeaves 24 24603648 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 384432) rows (by decide) (by decide)).symm.trans contract24027_0

theorem contract24027_1 : P.leaf 30 384433 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 487), (3, 1, 536), (11, 1, 879), (8, 0, 1266), (14, 0, 537), (5, 1, 433), (20, 1, 482), (21, 0, 488), (12, 1, 825), (30, 1, 867), (31, 1, 1217), (27, 1, 1601)]) (q := 1609) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c24027_1 : P.sumLeaves 24 24603712 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 384433) rows (by decide) (by decide)).symm.trans contract24027_1

theorem c24027_2 : P.sumLeaves 24 24603776 192 = 918049 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24027) (lo := 128) (len := 192) (W := 918049) check rows elimOK (by decide) (by decide) cover24027 (by decide)
  decide +kernel

theorem contract24027_3 : P.leaf 30 384437 = 25600 := by
  exact leaf_contract_factors (k := 30) (b := 21) (H := 384437) (ss := [(11, 1, 879), (8, 0, 1266), (14, 0, 537), (5, 1, 433), (20, 1, 482), (21, 0, 488), (12, 1, 818), (30, 1, 867), (31, 1, 1210)]) (ids := [0, 1, 2, 5, 7, 8, 11, 13, 14, 15, 16, 17, 20, 21, 22, 23, 25, 26, 4, 24, 27]) (cs := [2, 3, 4, 1, 20, 5, 0, 6, 7, 1, 1, 8, 0, 9, 10, 11, 12, 13, 1, 0, 14, 15, 16, 17, 21, 18, 19, 22, 1, 1]) (bs := [18, 3]) (W := 25600) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c24027_3 : P.sumLeaves 24 24603968 64 = 25600 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 384437) rows (by decide) (by decide)).symm.trans contract24027_3

theorem c24027_4 : P.sumLeaves 24 24604032 246 = 12979637 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24027) (lo := 384) (len := 246) (W := 12979637) check rows elimOK (by decide) (by decide) cover24027 (by decide)
  decide +kernel

theorem c24027_5 : P.sumLeaves 24 24604278 316 = 18073258 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24027) (lo := 630) (len := 316) (W := 18073258) check rows elimOK (by decide) (by decide) cover24027 (by decide)
  decide +kernel

theorem c24027_6 : P.sumLeaves 24 24604594 78 = 26935184 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24027) (lo := 946) (len := 78) (W := 26935184) check rows elimOK (by decide) (by decide) cover24027 (by decide)
  decide +kernel

theorem h24027 : P.leaf 34 24027 = 58931728 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 0), (64, 0), (192, 918049), (64, 25600), (246, 12979637), (316, 18073258), (78, 26935184)]) (.cons c24027_0 (.cons c24027_1 (.cons c24027_2 (.cons c24027_3 (.cons c24027_4 (.cons c24027_5 (.cons c24027_6 (.nil)))))))) (by decide) (by decide))

theorem cover24028 : P.CoversSplit 24 10 24028 0xff00ff00f000a000ff00ff00f000a000aa00000000000000aa00000000000000cc00cc0080008000cc00cc008000800088000000000000008800000000000000ff00ff00f000a000ff00ff00f000a000aa00000000000000aa000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 472, 516, 858, 916, 1202, 1210, 1601]) (ps := [(18, [867], [1210])]) (by decide +kernel)

theorem c24028_0 : P.sumLeaves 24 24604672 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24028) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover24028 (by decide)
  decide +kernel

theorem contract24028_1 : P.leaf 30 384452 = 0 := by
  exact leaf_contract_zero (ss := [(29, 1, 472), (18, 1, 867), (11, 1, 879), (8, 0, 1266), (20, 1, 531), (21, 1, 537)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c24028_1 : P.sumLeaves 24 24604928 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 384452) rows (by decide) (by decide)).symm.trans contract24028_1

theorem contract24028_2 : P.leaf 30 384453 = 0 := by
  exact leaf_contract_zero (ss := [(29, 1, 472), (18, 1, 867), (11, 1, 879), (8, 0, 1266), (20, 1, 531), (21, 1, 537)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c24028_2 : P.sumLeaves 24 24604992 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 384453) rows (by decide) (by decide)).symm.trans contract24028_2

theorem c24028_3 : P.sumLeaves 24 24605056 574 = 21102560 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24028) (lo := 384) (len := 574) (W := 21102560) check rows elimOK (by decide) (by decide) cover24028 (by decide)
  decide +kernel

theorem c24028_4 : P.sumLeaves 24 24605630 66 = 14412204 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24028) (lo := 958) (len := 66) (W := 14412204) check rows elimOK (by decide) (by decide) cover24028 (by decide)
  decide +kernel

theorem h24028 : P.leaf 34 24028 = 35514764 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 0), (64, 0), (574, 21102560), (66, 14412204)]) (.cons c24028_0 (.cons c24028_1 (.cons c24028_2 (.cons c24028_3 (.cons c24028_4 (.nil)))))) (by decide) (by decide))

theorem cover24029 : P.CoversSplit 24 10 24029 0xfffffffff0f0a0a0fffffffff0f0a0a0ffff000000005050ffff000000005050cccccccc80008000cc00cc0080008000cccc000040004000cc00000040004000ff00ff00f000a000ff33ff33f030a020ff00550000005000ff335511000050000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 516, 858, 865, 916, 1202, 1210, 1259, 1601]) (ps := [(14, [1217], [916])]) (by decide +kernel)

theorem c24029_0 : P.sumLeaves 24 24605696 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24029) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover24029 (by decide)
  decide +kernel

theorem contract24029_1 : P.leaf 30 384468 = 0 := by
  exact leaf_contract_zero (ss := [(11, 1, 879), (8, 0, 1266), (21, 0, 1266), (14, 1, 537), (20, 1, 580), (29, 1, 916)]) (q := 1658) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c24029_1 : P.sumLeaves 24 24605952 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 384468) rows (by decide) (by decide)).symm.trans contract24029_1

theorem contract24029_2 : P.leaf 30 384469 = 0 := by
  exact leaf_contract_zero (ss := [(11, 1, 879), (29, 1, 916), (8, 0, 1266), (21, 0, 1266), (14, 1, 537), (20, 1, 580)]) (q := 1658) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c24029_2 : P.sumLeaves 24 24606016 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 384469) rows (by decide) (by decide)).symm.trans contract24029_2

theorem c24029_3 : P.sumLeaves 24 24606080 379 = 22590396 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24029) (lo := 384) (len := 379) (W := 22590396) check rows elimOK (by decide) (by decide) cover24029 (by decide)
  decide +kernel

theorem c24029_4 : P.sumLeaves 24 24606459 226 = 34737471 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24029) (lo := 763) (len := 226) (W := 34737471) check rows elimOK (by decide) (by decide) cover24029 (by decide)
  decide +kernel

theorem c24029_5 : P.sumLeaves 24 24606685 35 = 25144486 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24029) (lo := 989) (len := 35) (W := 25144486) check rows elimOK (by decide) (by decide) cover24029 (by decide)
  decide +kernel

theorem h24029 : P.leaf 34 24029 = 82472353 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 0), (64, 0), (379, 22590396), (226, 34737471), (35, 25144486)]) (.cons c24029_0 (.cons c24029_1 (.cons c24029_2 (.cons c24029_3 (.cons c24029_4 (.cons c24029_5 (.nil))))))) (by decide) (by decide))

theorem cover24030 : P.CoversSplit 24 10 24030 0xfffffffff0f0a0a0fffffffff0f0a0a0aaaa000000000000aaaa000000000000ccc0ccc080008000cc00cc008000800088800000000000008800000000000000fffffffff0f0a0a0fffffffff0f0a0a0aaaa000000000000aaaa000000000000ccc0ccc080008000cc00cc008000800088000000000000008800000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 516, 858, 865, 1202, 1210, 1259, 1601]) (ps := [(8, [1609], [1266]), (18, [867], [1210])]) (by decide +kernel)

theorem c24030_0 : P.sumLeaves 24 24606720 256 = 3495462 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24030) (lo := 0) (len := 256) (W := 3495462) check rows elimOK (by decide) (by decide) cover24030 (by decide)
  decide +kernel

theorem contract24030_1 : P.leaf 30 384484 = 0 := by
  exact leaf_contract_zero (ss := [(18, 1, 867), (11, 1, 879), (8, 0, 1266), (20, 1, 531), (21, 1, 537), (5, 1, 565)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c24030_1 : P.sumLeaves 24 24606976 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 384484) rows (by decide) (by decide)).symm.trans contract24030_1

theorem contract24030_2 : P.leaf 30 384485 = 0 := by
  exact leaf_contract_zero (ss := [(18, 1, 867), (11, 1, 879), (8, 0, 1266), (20, 1, 531), (21, 1, 537)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c24030_2 : P.sumLeaves 24 24607040 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 384485) rows (by decide) (by decide)).symm.trans contract24030_2

theorem c24030_3 : P.sumLeaves 24 24607104 299 = 28404722 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24030) (lo := 384) (len := 299) (W := 28404722) check rows elimOK (by decide) (by decide) cover24030 (by decide)
  decide +kernel

theorem c24030_4 : P.sumLeaves 24 24607403 312 = 53467779 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24030) (lo := 683) (len := 312) (W := 53467779) check rows elimOK (by decide) (by decide) cover24030 (by decide)
  decide +kernel

theorem c24030_5 : P.sumLeaves 24 24607715 29 = 30121668 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24030) (lo := 995) (len := 29) (W := 30121668) check rows elimOK (by decide) (by decide) cover24030 (by decide)
  decide +kernel

theorem h24030 : P.leaf 34 24030 = 115489631 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 3495462), (64, 0), (64, 0), (299, 28404722), (312, 53467779), (29, 30121668)]) (.cons c24030_0 (.cons c24030_1 (.cons c24030_2 (.cons c24030_3 (.cons c24030_4 (.cons c24030_5 (.nil))))))) (by decide) (by decide))

theorem cover24031 : P.CoversSplit 24 10 24031 0xfffffffff0f0a0a0fffffffff0f0a0a0ffff000000005050ffff000000005050cccccccc80008000cc00cc0080008000cccc000040004000cc00000040004000fffffffff0f0a0a0fffffffff0f0a0a0ffff555500005050ffff555500005050cccccccc80008000cc00cc0080008000cc00440040004000cc00440040004000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 858, 865, 1202, 1210, 1259, 1601]) (ps := [(8, [1609], [1266])]) (by decide +kernel)

theorem contract24031_0 : P.leaf 30 384496 = 0 := by
  exact leaf_contract_zero (ss := [(3, 1, 536), (11, 1, 879), (29, 1, 1259), (8, 0, 1266), (5, 1, 565), (21, 0, 1266), (14, 1, 537), (20, 1, 1272), (27, 1, 1601)]) (q := 1658) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c24031_0 : P.sumLeaves 24 24607744 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 384496) rows (by decide) (by decide)).symm.trans contract24031_0

theorem contract24031_1 : P.leaf 30 384497 = 0 := by
  exact leaf_contract_zero (ss := [(3, 1, 536), (11, 1, 879), (8, 0, 1266), (5, 1, 622), (21, 0, 1266), (14, 1, 537), (20, 1, 1272), (27, 1, 1601), (29, 1, 1609)]) (q := 1658) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c24031_1 : P.sumLeaves 24 24607808 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 384497) rows (by decide) (by decide)).symm.trans contract24031_1

theorem c24031_2 : P.sumLeaves 24 24607872 128 = 7367896 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24031) (lo := 128) (len := 128) (W := 7367896) check rows elimOK (by decide) (by decide) cover24031 (by decide)
  decide +kernel

theorem contract24031_3 : P.leaf 30 384500 = 0 := by
  exact leaf_contract_zero (ss := [(11, 1, 879), (8, 0, 1266), (5, 1, 565), (21, 0, 1266), (14, 1, 537), (20, 1, 1272)]) (q := 1658) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c24031_3 : P.sumLeaves 24 24608000 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 384500) rows (by decide) (by decide)).symm.trans contract24031_3

theorem contract24031_4 : P.leaf 30 384501 = 0 := by
  exact leaf_contract_zero (ss := [(11, 1, 879), (8, 0, 1266), (21, 0, 1266), (14, 1, 537), (20, 1, 1272)]) (q := 1658) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c24031_4 : P.sumLeaves 24 24608064 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 384501) rows (by decide) (by decide)).symm.trans contract24031_4

theorem c24031_5 : P.sumLeaves 24 24608128 242 = 48156102 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24031) (lo := 384) (len := 242) (W := 48156102) check rows elimOK (by decide) (by decide) cover24031 (by decide)
  decide +kernel

theorem c24031_6 : P.sumLeaves 24 24608370 310 = 61457172 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24031) (lo := 626) (len := 310) (W := 61457172) check rows elimOK (by decide) (by decide) cover24031 (by decide)
  decide +kernel

theorem c24031_7 : P.sumLeaves 24 24608680 88 = 99572694 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24031) (lo := 936) (len := 88) (W := 99572694) check rows elimOK (by decide) (by decide) cover24031 (by decide)
  decide +kernel

theorem h24031 : P.leaf 34 24031 = 216553864 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 0), (64, 0), (128, 7367896), (64, 0), (64, 0), (242, 48156102), (310, 61457172), (88, 99572694)]) (.cons c24031_0 (.cons c24031_1 (.cons c24031_2 (.cons c24031_3 (.cons c24031_4 (.cons c24031_5 (.cons c24031_6 (.cons c24031_7 (.nil))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(24015, 24), (24026, 12), (24027, 24), (24028, 48), (24029, 48), (24030, 48), (24031, 48)]

theorem segOK : checkSeg 16 perms 24015 24044 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 24015 24044 252 24883152468 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 24883152468)
    (SegSum.cons (w := 24) h24015 (SegSum.cons (w := 12) h24026 (SegSum.cons (w := 24) h24027 (SegSum.cons (w := 48) h24028 (SegSum.cons (w := 48) h24029 (SegSum.cons (w := 48) h24030 (SegSum.cons (w := 48) h24031 (show SegSum (P.leaf 34) [] 0 from rfl)))))))) (by decide)

end RACert.S4N1.C0.S88
