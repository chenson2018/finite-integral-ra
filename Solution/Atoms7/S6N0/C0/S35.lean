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

namespace RACert.S6N0.C0.S35

open RACert RACert.Problem

theorem cover16383 : P.CoversSplit 26 10 16383 0xfffffffafffffac8fffffafafffffac8fffffffaffccfac8aa88aa88aa88aa88fffffafafffffac8aaaaaaaaaaaaaa88fffffafaffccfac8aa88aa88aa88aa88fffffffaffccfac8fffffafaffccfac8ffccffc8ffccfac8aa88aa88aa88aa88fffffafaffccfac8aaaaaaaaaa88aa88ffccfac8ffccfac8aa88aa88aa88aa88 :=
  coversSplit check rows (by decide) (by decide) (xs := [930, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c16383_0 : P.sumLeaves 26 16776192 128 = 5925904 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16383) (lo := 0) (len := 128) (W := 5925904) check rows elimOK (by decide) (by decide) cover16383 (by decide)
  decide +kernel

theorem contract16383_1 : P.leaf 32 262130 = 3112960 := by
  exact leaf_contract_factors (k := 32) (b := 22) (H := 262130) (ss := [(22, 1, 433), (2, 1, 482), (3, 1, 531), (4, 1, 580), (6, 1, 636), (7, 1, 825), (8, 1, 1217), (9, 1, 1609), (28, 1, 1658), (5, 1, 629)]) (ids := [9, 13, 14, 15, 17, 18, 27, 29, 31, 8, 10, 11, 12, 16, 19, 21, 22, 23, 24, 25, 28, 30]) (cs := [1, 1, 1, 1, 1, 1, 1, 1, 11, 2, 12, 13, 14, 3, 4, 5, 15, 6, 7, 16, 1, 17, 18, 19, 20, 21, 1, 8, 22, 9, 23, 10]) (bs := [9, 13]) (W := 3112960) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c16383_1 : P.sumLeaves 26 16776320 64 = 3112960 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 262130) rows (by decide) (by decide)).symm.trans contract16383_1

theorem contract16383_2 : P.leaf 32 262131 = 3822848 := by
  exact leaf_contract_factors (k := 32) (b := 23) (H := 262131) (ss := [(22, 1, 433), (2, 1, 482), (3, 1, 531), (4, 1, 580), (5, 1, 629), (6, 1, 636), (7, 1, 825), (8, 1, 1217), (9, 1, 1609)]) (ids := [9, 11, 13, 14, 15, 16, 17, 18, 19, 24, 26, 27, 28, 29, 30, 31, 8, 10, 12, 21, 22, 23, 25]) (cs := [1, 1, 1, 1, 1, 1, 1, 1, 18, 2, 19, 3, 20, 4, 5, 6, 7, 8, 9, 10, 1, 21, 22, 23, 11, 24, 12, 13, 14, 15, 16, 17]) (bs := [16, 7]) (W := 3822848) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c16383_2 : P.sumLeaves 26 16776384 64 = 3822848 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 262131) rows (by decide) (by decide)).symm.trans contract16383_2

theorem c16383_3 : P.sumLeaves 26 16776448 171 = 278638600 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16383) (lo := 256) (len := 171) (W := 278638600) check rows elimOK (by decide) (by decide) cover16383 (by decide)
  decide +kernel

theorem c16383_4 : P.sumLeaves 26 16776619 152 = 435543428 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16383) (lo := 427) (len := 152) (W := 435543428) check rows elimOK (by decide) (by decide) cover16383 (by decide)
  decide +kernel

theorem c16383_5 : P.sumLeaves 26 16776771 149 = 394693016 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16383) (lo := 579) (len := 149) (W := 394693016) check rows elimOK (by decide) (by decide) cover16383 (by decide)
  decide +kernel

theorem c16383_6 : P.sumLeaves 26 16776920 153 = 447257270 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16383) (lo := 728) (len := 153) (W := 447257270) check rows elimOK (by decide) (by decide) cover16383 (by decide)
  decide +kernel

theorem c16383_7 : P.sumLeaves 26 16777073 116 = 726429364 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16383) (lo := 881) (len := 116) (W := 726429364) check rows elimOK (by decide) (by decide) cover16383 (by decide)
  decide +kernel

theorem c16383_8 : P.sumLeaves 26 16777189 27 = 281616758 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16383) (lo := 997) (len := 27) (W := 281616758) check rows elimOK (by decide) (by decide) cover16383 (by decide)
  decide +kernel

theorem h16383 : P.leaf 36 16383 = 2577040148 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(128, 5925904), (64, 3112960), (64, 3822848), (171, 278638600), (152, 435543428), (149, 394693016), (153, 447257270), (116, 726429364), (27, 281616758)]) (.cons c16383_0 (.cons c16383_1 (.cons c16383_2 (.cons c16383_3 (.cons c16383_4 (.cons c16383_5 (.cons c16383_6 (.cons c16383_7 (.cons c16383_8 (.nil)))))))))) (by decide) (by decide))

theorem cover31200 : P.CoversSplit 26 10 31200 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c31200_0 : P.sumLeaves 26 31948800 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31200) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover31200 (by decide)
  decide +kernel

theorem h31200 : P.leaf 36 31200 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c31200_0 (.nil)) (by decide) (by decide))

theorem cover31201 : P.CoversSplit 26 10 31201 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c31201_0 : P.sumLeaves 26 31949824 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31201) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover31201 (by decide)
  decide +kernel

theorem h31201 : P.leaf 36 31201 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c31201_0 (.nil)) (by decide) (by decide))

theorem cover31203 : P.CoversSplit 26 10 31203 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c31203_0 : P.sumLeaves 26 31951872 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31203) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover31203 (by decide)
  decide +kernel

theorem h31203 : P.leaf 36 31203 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c31203_0 (.nil)) (by decide) (by decide))

theorem cover31205 : P.CoversSplit 26 10 31205 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c31205_0 : P.sumLeaves 26 31953920 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31205) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover31205 (by decide)
  decide +kernel

theorem h31205 : P.leaf 36 31205 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c31205_0 (.nil)) (by decide) (by decide))

theorem cover31207 : P.CoversSplit 26 10 31207 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c31207_0 : P.sumLeaves 26 31955968 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31207) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover31207 (by decide)
  decide +kernel

theorem h31207 : P.leaf 36 31207 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c31207_0 (.nil)) (by decide) (by decide))

theorem cover31215 : P.CoversSplit 26 10 31215 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c31215_0 : P.sumLeaves 26 31964160 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31215) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover31215 (by decide)
  decide +kernel

theorem h31215 : P.leaf 36 31215 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c31215_0 (.nil)) (by decide) (by decide))

theorem cover31217 : P.CoversSplit 26 10 31217 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c31217_0 : P.sumLeaves 26 31966208 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31217) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover31217 (by decide)
  decide +kernel

theorem h31217 : P.leaf 36 31217 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c31217_0 (.nil)) (by decide) (by decide))

theorem cover31219 : P.CoversSplit 26 10 31219 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c31219_0 : P.sumLeaves 26 31968256 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31219) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover31219 (by decide)
  decide +kernel

theorem h31219 : P.leaf 36 31219 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c31219_0 (.nil)) (by decide) (by decide))

theorem cover31220 : P.CoversSplit 26 10 31220 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c31220_0 : P.sumLeaves 26 31969280 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31220) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover31220 (by decide)
  decide +kernel

theorem h31220 : P.leaf 36 31220 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c31220_0 (.nil)) (by decide) (by decide))

theorem cover31221 : P.CoversSplit 26 10 31221 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c31221_0 : P.sumLeaves 26 31970304 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31221) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover31221 (by decide)
  decide +kernel

theorem h31221 : P.leaf 36 31221 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c31221_0 (.nil)) (by decide) (by decide))

theorem cover31223 : P.CoversSplit 26 10 31223 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c31223_0 : P.sumLeaves 26 31972352 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31223) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover31223 (by decide)
  decide +kernel

theorem h31223 : P.leaf 36 31223 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c31223_0 (.nil)) (by decide) (by decide))

theorem cover31228 : P.CoversSplit 26 10 31228 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c31228_0 : P.sumLeaves 26 31977472 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31228) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover31228 (by decide)
  decide +kernel

theorem h31228 : P.leaf 36 31228 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c31228_0 (.nil)) (by decide) (by decide))

theorem cover31229 : P.CoversSplit 26 10 31229 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c31229_0 : P.sumLeaves 26 31978496 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31229) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover31229 (by decide)
  decide +kernel

theorem h31229 : P.leaf 36 31229 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c31229_0 (.nil)) (by decide) (by decide))

theorem cover31231 : P.CoversSplit 26 10 31231 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c31231_0 : P.sumLeaves 26 31980544 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31231) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover31231 (by decide)
  decide +kernel

theorem h31231 : P.leaf 36 31231 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c31231_0 (.nil)) (by decide) (by decide))

theorem cover31440 : P.CoversSplit 26 10 31440 0x8000000080000000800000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 530, 587, 972, 979, 1265, 1273, 1315, 1322, 1665]) (by decide +kernel)

noncomputable def f31440 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 26 (32194560 + i)

theorem c31440_0 : rowSum f31440 0 1024 = 1040 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 31440) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover31440 (by decide)
  decide +kernel

theorem sum31440 : rowSum f31440 0 1024 = 1040 :=
  c31440_0

theorem h31440 : P.leaf 36 31440 = 1040 :=
  leaf_weighted (k := 26) (d := 10) (H := 31440) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 31440) (by decide) (by decide +kernel)) sum31440

theorem cover31441 : P.CoversSplit 26 10 31441 0x8000000080000000800000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 530, 587, 972, 979, 1273, 1315, 1322, 1665]) (by decide +kernel)

theorem c31441_0 : P.sumLeaves 26 32195584 1024 = 63376 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31441) (lo := 0) (len := 1024) (W := 63376) check rows elimOK (by decide) (by decide) cover31441 (by decide)
  decide +kernel

theorem h31441 : P.leaf 36 31441 = 63376 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 63376)]) (.cons c31441_0 (.nil)) (by decide) (by decide))

theorem cover31443 : P.CoversSplit 26 10 31443 0x8000000080000000800000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 530, 587, 972, 979, 1315, 1322]) (by decide +kernel)

noncomputable def f31443 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 26 (32197632 + i)

theorem c31443_0 : rowSum f31443 0 1024 = 1281360 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 31443) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover31443 (by decide)
  decide +kernel

theorem sum31443 : rowSum f31443 0 1024 = 1281360 :=
  c31443_0

theorem h31443 : P.leaf 36 31443 = 1281360 :=
  leaf_weighted (k := 26) (d := 10) (H := 31443) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 31443) (by decide) (by decide +kernel)) sum31443

theorem cover31446 : P.CoversSplit 26 10 31446 0xcc000000cc000400cc000000cc00000000000000000000000000000000000000040004000400040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 587, 880, 972, 979, 1265, 1315, 1658]) (by decide +kernel)

theorem c31446_0 : P.sumLeaves 26 32200704 1024 = 1740672 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31446) (lo := 0) (len := 1024) (W := 1740672) check rows elimOK (by decide) (by decide) cover31446 (by decide)
  decide +kernel

theorem h31446 : P.leaf 36 31446 = 1740672 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1740672)]) (.cons c31446_0 (.nil)) (by decide) (by decide))

theorem cover31447 : P.CoversSplit 26 10 31447 0xcc000000cc000400cc000000cc00000000000000000000000000000000000000040004000400040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 587, 972, 979, 1265, 1315, 1658]) (by decide +kernel)

theorem c31447_0 : P.sumLeaves 26 32201728 1024 = 11990400 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31447) (lo := 0) (len := 1024) (W := 11990400) check rows elimOK (by decide) (by decide) cover31447 (by decide)
  decide +kernel

theorem h31447 : P.leaf 36 31447 = 11990400 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 11990400)]) (.cons c31447_0 (.nil)) (by decide) (by decide))

theorem cover31455 : P.CoversSplit 26 10 31455 0xffff0000ffff0500ffff0000ffff000000000000000000000030000000000000050505050505050000000000000000000000000000000000000000000000000000330000000000000033000000000000003300000000000000300000000000000001000100000000000000000000000000010001000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 587, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f31455 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 26 (32209920 + i)

theorem c31455_0 : rowSum f31455 0 1024 = 75178080 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 31455) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover31455 (by decide)
  decide +kernel

theorem sum31455 : rowSum f31455 0 1024 = 75178080 :=
  c31455_0

theorem h31455 : P.leaf 36 31455 = 75178080 :=
  leaf_weighted (k := 26) (d := 10) (H := 31455) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 31455) (by decide) (by decide +kernel)) sum31455

theorem cover31472 : P.CoversSplit 26 10 31472 0xc000c000c000c000c0008000c000800000000000000000000000000000000000000000000000000000008000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 587, 972, 979, 1265, 1273, 1658, 1665]) (by decide +kernel)

theorem c31472_0 : P.sumLeaves 26 32227328 896 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31472) (lo := 0) (len := 896) (W := 0) check rows elimOK (by decide) (by decide) cover31472 (by decide)
  decide +kernel

theorem contract31472_1 : P.leaf 32 503566 = 5376 := by
  exact leaf_contract_factors (k := 32) (b := 19) (H := 503566) (ss := [(2, 1, 466), (7, 1, 475), (6, 1, 580), (3, 1, 409), (4, 1, 410), (5, 1, 411), (10, 1, 458), (11, 1, 459), (12, 1, 460), (13, 1, 461), (29, 1, 587), (31, 1, 979), (30, 1, 972)]) (ids := [6, 7, 12, 13, 14, 15, 16, 17, 18, 19, 20, 22, 23, 24, 26, 30, 31, 21, 25]) (cs := [1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 19, 13, 14, 15, 20, 16, 1, 1, 1, 17, 18]) (bs := [17, 2]) (W := 5376) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c31472_1 : P.sumLeaves 26 32228224 64 = 5376 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 503566) rows (by decide) (by decide)).symm.trans contract31472_1

theorem c31472_2 : P.sumLeaves 26 32228288 64 = 7232 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31472) (lo := 960) (len := 64) (W := 7232) check rows elimOK (by decide) (by decide) cover31472 (by decide)
  decide +kernel

theorem h31472 : P.leaf 36 31472 = 12608 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(896, 0), (64, 5376), (64, 7232)]) (.cons c31472_0 (.cons c31472_1 (.cons c31472_2 (.nil)))) (by decide) (by decide))

theorem cover31473 : P.CoversSplit 26 10 31473 0xc000c000c000c000c0008000c000800000000000000000000000000000000000000000000000000000008000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 587, 972, 979, 1265, 1273, 1658, 1665]) (by decide +kernel)

theorem c31473_0 : P.sumLeaves 26 32228352 1024 = 697952 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31473) (lo := 0) (len := 1024) (W := 697952) check rows elimOK (by decide) (by decide) cover31473 (by decide)
  decide +kernel

theorem h31473 : P.leaf 36 31473 = 697952 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 697952)]) (.cons c31473_0 (.nil)) (by decide) (by decide))

theorem cover31474 : P.CoversSplit 26 10 31474 0xc000c000c000c000c0008000c000800000000000000000000000000000000000000000000000000000008000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 587, 972, 979, 1265, 1658, 1665]) (by decide +kernel)

theorem c31474_0 : P.sumLeaves 26 32229376 1024 = 648560 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31474) (lo := 0) (len := 1024) (W := 648560) check rows elimOK (by decide) (by decide) cover31474 (by decide)
  decide +kernel

theorem h31474 : P.leaf 36 31474 = 648560 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 648560)]) (.cons c31474_0 (.nil)) (by decide) (by decide))

theorem cover31475 : P.CoversSplit 26 10 31475 0xc000c000c000c000c0008000c000800000000000000000000000000000000000000000000000000000008000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 587, 972, 979, 1265, 1658, 1665]) (by decide +kernel)

theorem c31475_0 : P.sumLeaves 26 32230400 1024 = 8471548 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31475) (lo := 0) (len := 1024) (W := 8471548) check rows elimOK (by decide) (by decide) cover31475 (by decide)
  decide +kernel

theorem h31475 : P.leaf 36 31475 = 8471548 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8471548)]) (.cons c31475_0 (.nil)) (by decide) (by decide))

theorem cover31477 : P.CoversSplit 26 10 31477 0xcc00cc00cc00c800cc008800cc00880000000000000000000000000000000000cc00c800cc00c800c0008000c00080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 587, 972, 979, 1265, 1273, 1315, 1658]) (by decide +kernel)

theorem c31477_0 : P.sumLeaves 26 32232448 1024 = 4721216 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31477) (lo := 0) (len := 1024) (W := 4721216) check rows elimOK (by decide) (by decide) cover31477 (by decide)
  decide +kernel

theorem h31477 : P.leaf 36 31477 = 4721216 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4721216)]) (.cons c31477_0 (.nil)) (by decide) (by decide))

theorem cover31478 : P.CoversSplit 26 10 31478 0xcc00cc00cc00c800cc008800cc00880000000000000000000000000000000000cc00c800cc00c800c0008000c00080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 587, 880, 972, 979, 1265, 1315, 1658]) (by decide +kernel)

theorem c31478_0 : P.sumLeaves 26 32233472 1024 = 10541504 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31478) (lo := 0) (len := 1024) (W := 10541504) check rows elimOK (by decide) (by decide) cover31478 (by decide)
  decide +kernel

theorem h31478 : P.leaf 36 31478 = 10541504 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 10541504)]) (.cons c31478_0 (.nil)) (by decide) (by decide))

theorem cover31479 : P.CoversSplit 26 10 31479 0xcc00cc00cc00c800cc008800cc00880000000000000000000000000000000000cc00c800cc00c800c0008000c00080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 587, 972, 979, 1265, 1315, 1658]) (by decide +kernel)

theorem c31479_0 : P.sumLeaves 26 32234496 1024 = 47906912 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31479) (lo := 0) (len := 1024) (W := 47906912) check rows elimOK (by decide) (by decide) cover31479 (by decide)
  decide +kernel

theorem h31479 : P.leaf 36 31479 = 47906912 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 47906912)]) (.cons c31479_0 (.nil)) (by decide) (by decide))

theorem cover31482 : P.CoversSplit 26 10 31482 0xf0f0f0f0f0f0f0c0f0f0a0a0f0f0a08000000000000000000030002000000000000000000000000000000000000000000000000000000000000000000000000000300030000000000030002000000000003000300000000000300020000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 587, 874, 972, 979, 1265, 1273, 1322, 1665]) (by decide +kernel)

theorem c31482_0 : P.sumLeaves 26 32237568 320 = 71488 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31482) (lo := 0) (len := 320) (W := 71488) check rows elimOK (by decide) (by decide) cover31482 (by decide)
  decide +kernel

theorem contract31482_1 : P.leaf 32 503717 = 113856 := by
  exact leaf_contract_factors (k := 32) (b := 20) (H := 503717) (ss := [(2, 1, 482), (21, 1, 536), (10, 1, 867), (30, 1, 972), (29, 0, 1665), (16, 1, 1273), (33, 1, 1273), (19, 1, 1259), (31, 0, 1665), (27, 1, 489), (17, 1, 1322), (14, 1, 858)]) (ids := [1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 13, 16, 18, 20, 21, 26, 30, 22, 23, 24]) (cs := [1, 2, 3, 4, 5, 6, 7, 8, 1, 9, 10, 11, 1, 12, 1, 1, 13, 1, 14, 1, 15, 16, 19, 20, 21, 1, 17, 0, 1, 0, 18, 1]) (bs := [17, 3]) (W := 113856) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c31482_1 : P.sumLeaves 26 32237888 64 = 113856 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 503717) rows (by decide) (by decide)).symm.trans contract31482_1

theorem c31482_2 : P.sumLeaves 26 32237952 64 = 20736 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31482) (lo := 384) (len := 64) (W := 20736) check rows elimOK (by decide) (by decide) cover31482 (by decide)
  decide +kernel

theorem contract31482_3 : P.leaf 32 503719 = 145872 := by
  exact leaf_contract_factors (k := 32) (b := 20) (H := 503719) (ss := [(2, 1, 482), (30, 1, 972), (20, 0, 1665), (9, 1, 1609), (19, 1, 1259), (21, 1, 1259), (29, 0, 1665), (31, 0, 1665), (17, 1, 1322), (14, 1, 858), (16, 1, 858), (33, 1, 1322)]) (ids := [1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 13, 16, 20, 21, 25, 26, 30, 22, 23, 24]) (cs := [1, 2, 3, 4, 5, 6, 7, 1, 8, 9, 10, 11, 1, 12, 1, 1, 13, 1, 0, 1, 14, 15, 19, 20, 21, 16, 17, 0, 1, 0, 18, 1]) (bs := [17, 3]) (W := 145872) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c31482_3 : P.sumLeaves 26 32238016 64 = 145872 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 503719) rows (by decide) (by decide)).symm.trans contract31482_3

theorem c31482_4 : P.sumLeaves 26 32238080 512 = 18174368 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31482) (lo := 512) (len := 512) (W := 18174368) check rows elimOK (by decide) (by decide) cover31482 (by decide)
  decide +kernel

theorem h31482 : P.leaf 36 31482 = 18526320 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(320, 71488), (64, 113856), (64, 20736), (64, 145872), (512, 18174368)]) (.cons c31482_0 (.cons c31482_1 (.cons c31482_2 (.cons c31482_3 (.cons c31482_4 (.nil)))))) (by decide) (by decide))

theorem cover31483 : P.CoversSplit 26 10 31483 0xf0f0f0f0f0f0f0c0f0f0a0a0f0f0a08000000000000000000030002000000000000000000000000000000000000000000000000000000000000000000000000000300030000000000030002000000000003000300000000000300020000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 587, 972, 979, 1265, 1273, 1322, 1665]) (by decide +kernel)

theorem c31483_0 : P.sumLeaves 26 32238592 320 = 207872 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31483) (lo := 0) (len := 320) (W := 207872) check rows elimOK (by decide) (by decide) cover31483 (by decide)
  decide +kernel

theorem contract31483_1 : P.leaf 32 503733 = 327936 := by
  exact leaf_contract_factors (k := 32) (b := 21) (H := 503733) (ss := [(2, 1, 482), (21, 1, 586), (10, 1, 867), (30, 1, 972), (29, 0, 1665), (16, 1, 1273), (33, 1, 1273), (19, 1, 1259), (31, 0, 1665), (27, 1, 930), (17, 1, 1322)]) (ids := [1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 13, 16, 18, 20, 21, 26, 12, 22, 23, 24, 30]) (cs := [1, 2, 3, 4, 5, 6, 7, 8, 1, 9, 10, 11, 18, 12, 1, 1, 13, 1, 14, 1, 15, 16, 19, 20, 21, 1, 17, 0, 1, 0, 22, 1]) (bs := [16, 5]) (W := 327936) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c31483_1 : P.sumLeaves 26 32238912 64 = 327936 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 503733) rows (by decide) (by decide)).symm.trans contract31483_1

theorem c31483_2 : P.sumLeaves 26 32238976 640 = 77277108 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31483) (lo := 384) (len := 640) (W := 77277108) check rows elimOK (by decide) (by decide) cover31483 (by decide)
  decide +kernel

theorem h31483 : P.leaf 36 31483 = 77812916 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(320, 207872), (64, 327936), (640, 77277108)]) (.cons c31483_0 (.cons c31483_1 (.cons c31483_2 (.nil)))) (by decide) (by decide))

theorem cover31487 : P.CoversSplit 26 10 31487 0xfffffffffffffac8ffffaaaaffffaa8800000000000000000030002000000000fffffafafffffac8f0f0a0a0f0f0a0800000000000000000003000200000000000330033000000000033002200000000003300330000000000300020000000000033003200000000003000200000000000330032000000000030002000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c31487_0 : P.sumLeaves 26 32242688 64 = 3712 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31487) (lo := 0) (len := 64) (W := 3712) check rows elimOK (by decide) (by decide) cover31487 (by decide)
  decide +kernel

theorem contract31487_1 : P.leaf 32 503793 = 8096 := by
  exact leaf_contract_factors (k := 32) (b := 15) (H := 503793) (ss := [(22, 1, 433), (2, 1, 482), (3, 1, 531), (4, 1, 580), (7, 1, 825), (10, 1, 867), (8, 1, 1217), (9, 1, 1609), (19, 1, 1259), (21, 1, 1259), (29, 0, 1665), (16, 1, 1273), (33, 1, 1273), (6, 1, 636), (31, 0, 1665), (27, 1, 930), (17, 1, 1322)]) (ids := [3, 9, 12, 13, 16, 21, 24, 26, 28, 30, 10, 11, 18, 22, 23]) (cs := [1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 12, 13, 4, 5, 1, 1, 6, 1, 14, 1, 1, 7, 15, 16, 8, 1, 9, 0, 10, 0, 11, 1]) (bs := [10, 5]) (W := 8096) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c31487_1 : P.sumLeaves 26 32242752 64 = 8096 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 503793) rows (by decide) (by decide)).symm.trans contract31487_1

theorem c31487_2 : P.sumLeaves 26 32242816 64 = 9696 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31487) (lo := 128) (len := 64) (W := 9696) check rows elimOK (by decide) (by decide) cover31487 (by decide)
  decide +kernel

theorem contract31487_3 : P.leaf 32 503795 = 23984 := by
  exact leaf_contract_factors (k := 32) (b := 17) (H := 503795) (ss := [(22, 1, 433), (2, 1, 482), (3, 1, 531), (4, 1, 580), (6, 1, 636), (7, 1, 825), (8, 1, 1217), (9, 1, 1609), (19, 1, 1259), (21, 1, 1259), (20, 0, 1665), (29, 0, 1665), (31, 0, 1665), (17, 1, 1322), (33, 1, 1322)]) (ids := [3, 8, 9, 10, 11, 12, 13, 14, 16, 21, 22, 24, 25, 26, 28, 30, 23]) (cs := [1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 5, 6, 7, 8, 9, 1, 10, 1, 0, 1, 1, 11, 12, 18, 13, 14, 15, 0, 16, 0, 17, 1]) (bs := [16, 1]) (W := 23984) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c31487_3 : P.sumLeaves 26 32242880 64 = 23984 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 503795) rows (by decide) (by decide)).symm.trans contract31487_3

theorem c31487_4 : P.sumLeaves 26 32242944 504 = 67659452 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31487) (lo := 256) (len := 504) (W := 67659452) check rows elimOK (by decide) (by decide) cover31487 (by decide)
  decide +kernel

theorem c31487_5 : P.sumLeaves 26 32243448 246 = 193210912 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31487) (lo := 760) (len := 246) (W := 193210912) check rows elimOK (by decide) (by decide) cover31487 (by decide)
  decide +kernel

theorem c31487_6 : P.sumLeaves 26 32243694 18 = 59317168 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31487) (lo := 1006) (len := 18) (W := 59317168) check rows elimOK (by decide) (by decide) cover31487 (by decide)
  decide +kernel

theorem h31487 : P.leaf 36 31487 = 320233020 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 3712), (64, 8096), (64, 9696), (64, 23984), (504, 67659452), (246, 193210912), (18, 59317168)]) (.cons c31487_0 (.cons c31487_1 (.cons c31487_2 (.cons c31487_3 (.cons c31487_4 (.cons c31487_5 (.cons c31487_6 (.nil)))))))) (by decide) (by decide))

theorem cover31728 : P.CoversSplit 26 10 31728 0xf000f000f000f000f000a000f000a000f000f000c000c000f000a000c000800800000000000000000000aa000000aa0000000000000000000000aa00000088080000000000000000000000000000000000000000c0c0c0c000000000c0c080880000000000000000000000000000000000000000000000000000000000008888 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 972, 979, 1265, 1273]) (by decide +kernel)

noncomputable def f31728 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (32489472 + i)

theorem c31728_0 : rowSum f31728 0 1024 = 201550 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 31728) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover31728 (by decide)
  decide +kernel

theorem sum31728 : rowSum f31728 0 1024 = 201550 :=
  c31728_0

theorem h31728 : P.leaf 36 31728 = 201550 :=
  leaf_weighted (k := 26) (d := 10) (H := 31728) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 31728) (by decide) (by decide +kernel)) sum31728

def seg : List (ℕ × ℕ) := [(16383, 360), (31200, 15), (31201, 180), (31203, 90), (31205, 180), (31207, 180), (31215, 45), (31217, 180), (31219, 180), (31220, 360), (31221, 720), (31223, 360), (31228, 180), (31229, 360), (31231, 180), (31440, 90), (31441, 360), (31443, 360), (31446, 180), (31447, 360), (31455, 90), (31472, 360), (31473, 720), (31474, 720), (31475, 720), (31477, 360), (31478, 720), (31479, 720), (31482, 360), (31483, 720), (31487, 360), (31728, 90)]

theorem segOK : checkSeg 20 perms 16383 31729 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 16383 31729 10860 1168467384780 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1168467384780)
    (SegSum.cons (w := 360) h16383 (SegSum.cons (w := 15) h31200 (SegSum.cons (w := 180) h31201 (SegSum.cons (w := 90) h31203 (SegSum.cons (w := 180) h31205 (SegSum.cons (w := 180) h31207 (SegSum.cons (w := 45) h31215 (SegSum.cons (w := 180) h31217 (SegSum.cons (w := 180) h31219 (SegSum.cons (w := 360) h31220 (SegSum.cons (w := 720) h31221 (SegSum.cons (w := 360) h31223 (SegSum.cons (w := 180) h31228 (SegSum.cons (w := 360) h31229 (SegSum.cons (w := 180) h31231 (SegSum.cons (w := 90) h31440 (SegSum.cons (w := 360) h31441 (SegSum.cons (w := 360) h31443 (SegSum.cons (w := 180) h31446 (SegSum.cons (w := 360) h31447 (SegSum.cons (w := 90) h31455 (SegSum.cons (w := 360) h31472 (SegSum.cons (w := 720) h31473 (SegSum.cons (w := 720) h31474 (SegSum.cons (w := 720) h31475 (SegSum.cons (w := 360) h31477 (SegSum.cons (w := 720) h31478 (SegSum.cons (w := 720) h31479 (SegSum.cons (w := 360) h31482 (SegSum.cons (w := 720) h31483 (SegSum.cons (w := 360) h31487 (SegSum.cons (w := 90) h31728 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S35
