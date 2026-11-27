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

theorem cover22527 : P.CoversSplit 24 10 22527 0xfffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaacccccccc88888888cccccccc88888888cccccccc88888888cccccccc88888888fffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaacccccccc88888888cccccccc88888888cccccccc88888888cccccccc88888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [860, 916, 1202, 1210, 1601]) (by decide +kernel)

theorem c22527_0 : P.sumLeaves 24 23067648 257 = 58419756 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22527) (lo := 0) (len := 257) (W := 58419756) check rows elimOK (by decide) (by decide) cover22527 (by decide)
  decide +kernel

theorem c22527_1 : P.sumLeaves 24 23067905 119 = 66971620 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22527) (lo := 257) (len := 119) (W := 66971620) check rows elimOK (by decide) (by decide) cover22527 (by decide)
  decide +kernel

theorem c22527_2 : P.sumLeaves 24 23068024 120 = 119496676 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22527) (lo := 376) (len := 120) (W := 119496676) check rows elimOK (by decide) (by decide) cover22527 (by decide)
  decide +kernel

theorem c22527_3 : P.sumLeaves 24 23068144 242 = 141219640 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22527) (lo := 496) (len := 242) (W := 141219640) check rows elimOK (by decide) (by decide) cover22527 (by decide)
  decide +kernel

theorem c22527_4 : P.sumLeaves 24 23068386 134 = 150800743 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22527) (lo := 738) (len := 134) (W := 150800743) check rows elimOK (by decide) (by decide) cover22527 (by decide)
  decide +kernel

theorem c22527_5 : P.sumLeaves 24 23068520 120 = 253984811 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22527) (lo := 872) (len := 120) (W := 253984811) check rows elimOK (by decide) (by decide) cover22527 (by decide)
  decide +kernel

theorem c22527_6 : P.sumLeaves 24 23068640 32 = 103409480 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22527) (lo := 992) (len := 32) (W := 103409480) check rows elimOK (by decide) (by decide) cover22527 (by decide)
  decide +kernel

theorem h22527 : P.leaf 34 22527 = 894302726 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(257, 58419756), (119, 66971620), (120, 119496676), (242, 141219640), (134, 150800743), (120, 253984811), (32, 103409480)]) (.cons c22527_0 (.cons c22527_1 (.cons c22527_2 (.cons c22527_3 (.cons c22527_4 (.cons c22527_5 (.cons c22527_6 (.nil)))))))) (by decide) (by decide))

theorem cover23788 : P.CoversSplit 24 10 23788 0xffffffffeae00000ffffffffeae00000ffff00000000a0a0ffff00000000a0800000000000000000000000000000000000000000000000000000000000000000cc00cc00c80000000000000000000000cc00cc000000800000330033000000200000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 573, 858, 865, 916, 1210, 1259, 1601]) (ps := [(17, [1259], [1251])]) (by decide +kernel)

noncomputable def f23788 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (24358912 + i)

theorem c23788_0 : rowSum f23788 0 1023 = 8326213 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 23788) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover23788 (by decide)
  decide +kernel

theorem c23788_1 : rowSum f23788 1023 1 = 347280 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 23788) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover23788 (by decide)
  decide +kernel

theorem sum23788 : rowSum f23788 0 1024 = 8673493 :=
  rowSum_append (F := f23788) (lo := 0) (n := 1023) (m := 1) (A := 8326213) (B := 347280) c23788_0 (c23788_1)

theorem h23788 : P.leaf 34 23788 = 8673493 :=
  leaf_weighted (k := 24) (d := 10) (H := 23788) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 23788) (by decide) (by decide +kernel)) sum23788

theorem cover23789 : P.CoversSplit 24 10 23789 0xffffffffeae00000ffffffffeae00000ffff00000000a0a0ffff00000000a0800000000000000000000000000000000000000000000000000000000000000000cc00cc00c80000000000000000000000cc00cc000000800000330033000000200000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 522, 573, 858, 865, 916, 1202, 1210, 1259, 1601]) (ps := [(17, [1259], [1251])]) (by decide +kernel)

noncomputable def f23789 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (24359936 + i)

theorem c23789_0 : rowSum f23789 0 1023 = 11412103 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 23789) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover23789 (by decide)
  decide +kernel

theorem c23789_1 : rowSum f23789 1023 1 = 427432 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 23789) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover23789 (by decide)
  decide +kernel

theorem sum23789 : rowSum f23789 0 1024 = 11839535 :=
  rowSum_append (F := f23789) (lo := 0) (n := 1023) (m := 1) (A := 11412103) (B := 427432) c23789_0 (c23789_1)

theorem h23789 : P.leaf 34 23789 = 11839535 :=
  leaf_weighted (k := 24) (d := 10) (H := 23789) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 23789) (by decide) (by decide +kernel)) sum23789

theorem cover23790 : P.CoversSplit 24 10 23790 0xfffffffffafa0000fffffffffafa0000ffff00000000fafaffff00000000fac80000000000000000000000000000000000000000000000000000000000000000cc00cc00c80000000000000000000000cc0000000000c80000330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 522, 573, 858, 865, 916, 1202, 1210, 1259, 1601]) (ps := [(8, [565], [573]), (17, [1259], [1251]), (18, [536], [1210])]) (by decide +kernel)

noncomputable def f23790 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (24360960 + i)

theorem c23790_0 : rowSum f23790 0 1013 = 28052286 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 23790) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover23790 (by decide)
  decide +kernel

theorem c23790_1 : rowSum f23790 1013 11 = 7068312 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 23790) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover23790 (by decide)
  decide +kernel

theorem sum23790 : rowSum f23790 0 1024 = 35120598 :=
  rowSum_append (F := f23790) (lo := 0) (n := 1013) (m := 11) (A := 28052286) (B := 7068312) c23790_0 (c23790_1)

theorem h23790 : P.leaf 34 23790 = 35120598 :=
  leaf_weighted (k := 24) (d := 10) (H := 23790) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 23790) (by decide) (by decide +kernel)) sum23790

theorem cover23791 : P.CoversSplit 24 10 23791 0xfffffffffafa0000fffffffffafa0000ffff00000000fafaffff00000000fac80000000000000000000000000000000000000000000000000000000000000000cc00cc00c80000000000000000000000cc0000000000c80000330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 573, 858, 865, 916, 1202, 1210, 1259, 1601]) (ps := [(8, [565], [573]), (17, [1259], [1251]), (18, [536], [1210])]) (by decide +kernel)

noncomputable def f23791 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (24361984 + i)

theorem c23791_0 : rowSum f23791 0 1013 = 36858799 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 23791) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover23791 (by decide)
  decide +kernel

theorem c23791_1 : rowSum f23791 1013 11 = 9022940 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 23791) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover23791 (by decide)
  decide +kernel

theorem sum23791 : rowSum f23791 0 1024 = 45881739 :=
  rowSum_append (F := f23791) (lo := 0) (n := 1013) (m := 11) (A := 36858799) (B := 9022940) c23791_0 (c23791_1)

theorem h23791 : P.leaf 34 23791 = 45881739 :=
  leaf_weighted (k := 24) (d := 10) (H := 23791) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 23791) (by decide) (by decide +kernel)) sum23791

theorem cover23806 : P.CoversSplit 24 10 23806 0xfffffffffafa0000fffffffffafa0000fffffffffafa0000fffffffffafa00000000000000000000000000000000000000000000000000000000000000000000cc00cc00c80000000000000000000000cc00cc00c000000000330033002000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 573, 858, 865, 916, 1202, 1210, 1259, 1601]) (ps := [(8, [1217], [573, 1266]), (14, [1217], [916])]) (by decide +kernel)

theorem c23806_0 : P.sumLeaves 24 24377344 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23806) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover23806 (by decide)
  decide +kernel

theorem contract23806_1 : P.leaf 30 380900 = 4320 := by
  apply (leaf_contract (k := 30) (b := 14) (H := 380900) (ss := [(18, 1, 867), (17, 0, 1259), (27, 0, 1259), (8, 0, 573), (9, 0, 573), (29, 0, 573), (14, 0, 580), (5, 1, 433), (21, 0, 580), (20, 1, 433), (7, 1, 628), (15, 0, 678), (12, 1, 825), (13, 1, 971), (31, 1, 1217), (16, 1, 1314)]) (ids := [0, 1, 2, 4, 8, 9, 17, 20, 21, 22, 23, 24, 26, 28]) (cs := [2, 3, 4, 1, 5, 1, 0, 0, 6, 7, 1, 1, 0, 0, 1, 0, 1, 8, 1, 0, 9, 10, 11, 12, 13, 0, 14, 0, 15, 1]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c23806_1 : P.sumLeaves 24 24377600 64 = 4320 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 380900) rows (by decide) (by decide)).symm.trans contract23806_1

theorem contract23806_2 : P.leaf 30 380901 = 13952 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 380901) (ss := [(27, 1, 573), (18, 1, 867), (29, 1, 916), (8, 0, 1266), (14, 0, 580), (5, 1, 433), (21, 0, 580), (20, 1, 433), (7, 1, 628), (12, 1, 825), (13, 1, 971), (31, 1, 1217), (16, 1, 1314)]) (ids := [0, 1, 2, 4, 7, 8, 9, 13, 15, 17, 20, 21, 22, 24, 26, 28, 23]) (cs := [2, 3, 4, 1, 5, 1, 0, 6, 7, 8, 1, 1, 0, 9, 1, 10, 1, 11, 1, 0, 12, 13, 14, 18, 15, 1, 16, 1, 17, 1]) (bs := [16, 1]) (W := 13952) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c23806_2 : P.sumLeaves 24 24377664 64 = 13952 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 380901) rows (by decide) (by decide)).symm.trans contract23806_2

theorem c23806_3 : P.sumLeaves 24 24377728 509 = 26640607 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23806) (lo := 384) (len := 509) (W := 26640607) check rows elimOK (by decide) (by decide) cover23806 (by decide)
  decide +kernel

theorem c23806_4 : P.sumLeaves 24 24378237 131 = 69896520 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23806) (lo := 893) (len := 131) (W := 69896520) check rows elimOK (by decide) (by decide) cover23806 (by decide)
  decide +kernel

theorem h23806 : P.leaf 34 23806 = 96555399 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 4320), (64, 13952), (509, 26640607), (131, 69896520)]) (.cons c23806_0 (.cons c23806_1 (.cons c23806_2 (.cons c23806_3 (.cons c23806_4 (.nil)))))) (by decide) (by decide))

theorem cover23807 : P.CoversSplit 24 10 23807 0xfffffffffafa0000fffffffffafa0000fffffffffafa0000fffffffffafa00000000000000000000000000000000000000000000000000000000000000000000cc00cc00c80000000000000000000000cc00cc00c000000000330033002000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [573, 858, 865, 916, 1202, 1210, 1259, 1601]) (ps := [(8, [1217], [573, 1266]), (14, [1217], [916])]) (by decide +kernel)

theorem c23807_0 : P.sumLeaves 24 24378368 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23807) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover23807 (by decide)
  decide +kernel

theorem contract23807_1 : P.leaf 30 380916 = 8232 := by
  apply (leaf_contract (k := 30) (b := 14) (H := 380916) (ss := [(18, 1, 867), (17, 0, 1259), (27, 0, 1259), (8, 0, 573), (9, 0, 573), (29, 0, 573), (14, 0, 580), (5, 1, 433), (21, 0, 580), (20, 1, 433), (7, 1, 628), (15, 0, 678), (12, 1, 825), (13, 1, 971), (31, 1, 1217), (16, 1, 1314)]) (ids := [0, 1, 2, 4, 8, 9, 17, 20, 21, 22, 23, 24, 26, 28]) (cs := [2, 3, 4, 1, 5, 1, 0, 0, 6, 7, 1, 1, 0, 0, 1, 0, 1, 8, 1, 0, 9, 10, 11, 12, 13, 0, 14, 0, 15, 1]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c23807_1 : P.sumLeaves 24 24378624 64 = 8232 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 380916) rows (by decide) (by decide)).symm.trans contract23807_1

theorem contract23807_2 : P.leaf 30 380917 = 19168 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 380917) (ss := [(27, 1, 573), (18, 1, 867), (29, 1, 916), (8, 0, 1266), (14, 0, 580), (5, 1, 433), (21, 0, 580), (20, 1, 433), (7, 1, 628), (12, 1, 825), (13, 1, 971), (31, 1, 1217), (16, 1, 1314)]) (ids := [0, 1, 2, 4, 7, 8, 9, 13, 15, 17, 20, 21, 22, 24, 26, 28, 23]) (cs := [2, 3, 4, 1, 5, 1, 0, 6, 7, 8, 1, 1, 0, 9, 1, 10, 1, 11, 1, 0, 12, 13, 14, 18, 15, 1, 16, 1, 17, 1]) (bs := [16, 1]) (W := 19168) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c23807_2 : P.sumLeaves 24 24378688 64 = 19168 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 380917) rows (by decide) (by decide)).symm.trans contract23807_2

theorem c23807_3 : P.sumLeaves 24 24378752 509 = 33868563 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23807) (lo := 384) (len := 509) (W := 33868563) check rows elimOK (by decide) (by decide) cover23807 (by decide)
  decide +kernel

theorem c23807_4 : P.sumLeaves 24 24379261 131 = 81278104 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23807) (lo := 893) (len := 131) (W := 81278104) check rows elimOK (by decide) (by decide) cover23807 (by decide)
  decide +kernel

theorem h23807 : P.leaf 34 23807 = 115174067 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 8232), (64, 19168), (509, 33868563), (131, 81278104)]) (.cons c23807_0 (.cons c23807_1 (.cons c23807_2 (.cons c23807_3 (.cons c23807_4 (.nil)))))) (by decide) (by decide))

theorem cover23844 : P.CoversSplit 24 10 23844 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c23844_0 : P.sumLeaves 24 24416256 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23844) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover23844 (by decide)
  decide +kernel

theorem h23844 : P.leaf 34 23844 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c23844_0 (.nil)) (by decide) (by decide))

theorem cover23845 : P.CoversSplit 24 10 23845 0x8800000088000000000000000000000088000000000000000000000000000000880000008800000000000000000000008800000000000000000000000000000088000000880000000000000000000000880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [466, 473, 515, 522, 529, 572, 858, 865, 916, 1210, 1601]) (by decide +kernel)

theorem c23845_0 : P.sumLeaves 24 24417280 1024 = 497537 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23845) (lo := 0) (len := 1024) (W := 497537) check rows elimOK (by decide) (by decide) cover23845 (by decide)
  decide +kernel

theorem h23845 : P.leaf 34 23845 = 497537 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 497537)]) (.cons c23845_0 (.nil)) (by decide) (by decide))

theorem cover23846 : P.CoversSplit 24 10 23846 0x8888000088880000000000000000000088880000000000000000000000000000888000008880000000000000000000008880000000000000000000000000000088880000888800000000000000000000888800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 466, 515, 517, 522, 529, 858, 865, 1202, 1259]) (by decide +kernel)

theorem c23846_0 : P.sumLeaves 24 24418304 1024 = 2923776 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23846) (lo := 0) (len := 1024) (W := 2923776) check rows elimOK (by decide) (by decide) cover23846 (by decide)
  decide +kernel

theorem h23846 : P.leaf 34 23846 = 2923776 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2923776)]) (.cons c23846_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(22527, 24), (23788, 8), (23789, 8), (23790, 24), (23791, 24), (23806, 24), (23807, 24), (23844, 12), (23845, 24), (23846, 24)]

theorem segOK : checkSeg 16 perms 22527 23847 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 22527 23847 196 28735044432 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 28735044432)
    (SegSum.cons (w := 24) h22527 (SegSum.cons (w := 8) h23788 (SegSum.cons (w := 8) h23789 (SegSum.cons (w := 24) h23790 (SegSum.cons (w := 24) h23791 (SegSum.cons (w := 24) h23806 (SegSum.cons (w := 24) h23807 (SegSum.cons (w := 12) h23844 (SegSum.cons (w := 24) h23845 (SegSum.cons (w := 24) h23846 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))) (by decide)

end RACert.S4N1.C0.S82
