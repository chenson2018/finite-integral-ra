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

namespace RACert.S6N0.C0.S39

open RACert RACert.Problem

theorem cover65527 : P.CoversSplit 26 10 65527 0xfffffffffffffac8fffffafafffffac8ffffffffffccfac8fac8fac8fac8fac8fffffafafffffac8fafafafafafafac8fffffafaffccfac8fac8fac8fac8fac8ffffffffffccfac8fffffafaffccfac8ffccffccffccfac8fac8fac8fac8fac8fffffafaffccfac8fafafafafac8fac8ffccfac8ffccfac8fac8fac8fac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f65527 (i : ℕ) := rowWeight keep9 twice9 i * P.leaf 26 (67099648 + i)

theorem c65527_0 : rowSum f65527 0 279 = 501010080 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 65527) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover65527 (by decide)
  decide +kernel

theorem c65527_1 : rowSum f65527 279 256 = 1132391536 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 65527) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover65527 (by decide)
  decide +kernel

theorem c65527_2 : rowSum f65527 535 256 = 970032488 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 65527) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover65527 (by decide)
  decide +kernel

theorem c65527_3 : rowSum f65527 791 232 = 1337977160 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 65527) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover65527 (by decide)
  decide +kernel

theorem c65527_4 : rowSum f65527 1023 1 = 18415400 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 65527) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover65527 (by decide)
  decide +kernel

theorem sum65527 : rowSum f65527 0 1024 = 3959826664 :=
  rowSum_append (F := f65527) (lo := 0) (n := 279) (m := 745) (A := 501010080) (B := 3458816584) c65527_0 (rowSum_append (F := f65527) (lo := 279) (n := 256) (m := 489) (A := 1132391536) (B := 2326425048) c65527_1 (rowSum_append (F := f65527) (lo := 535) (n := 256) (m := 233) (A := 970032488) (B := 1356392560) c65527_2 (rowSum_append (F := f65527) (lo := 791) (n := 232) (m := 1) (A := 1337977160) (B := 18415400) c65527_3 (c65527_4))))

theorem h65527 : P.leaf 36 65527 = 3959826664 :=
  leaf_weighted (k := 26) (d := 10) (H := 65527) (keep := keep9) (twice := twice9) rows (by decide) (by decide) bal9 (invRow9 (H := 65527) (by decide) (by decide +kernel)) sum65527

theorem cover65535 : P.CoversSplit 26 10 65535 0xfffffffffffffac8fffffafafffffac8ffffffffffccfac8fac8fac8fac8fac8fffffafafffffac8fafafafafafafac8fffffafaffccfac8fac8fac8fac8fac8ffffffffffccfac8fffffafaffccfac8ffccffccffccfac8fac8fac8fac8fac8fffffafaffccfac8fafafafafac8fac8ffccfac8ffccfac8fac8fac8fac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f65535 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (67107840 + i)

theorem c65535_0 : rowSum f65535 0 268 = 1993478328 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 65535) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65535 (by decide)
  decide +kernel

theorem c65535_1 : rowSum f65535 268 147 = 2684633412 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 65535) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65535 (by decide)
  decide +kernel

theorem c65535_2 : rowSum f65535 415 384 = 2993507876 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 65535) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65535 (by decide)
  decide +kernel

theorem c65535_3 : rowSum f65535 799 225 = 2865275576 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 65535) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65535 (by decide)
  decide +kernel

theorem sum65535 : rowSum f65535 0 1024 = 10536895192 :=
  rowSum_append (F := f65535) (lo := 0) (n := 268) (m := 756) (A := 1993478328) (B := 8543416864) c65535_0 (rowSum_append (F := f65535) (lo := 268) (n := 147) (m := 609) (A := 2684633412) (B := 5858783452) c65535_1 (rowSum_append (F := f65535) (lo := 415) (n := 384) (m := 225) (A := 2993507876) (B := 2865275576) c65535_2 (c65535_3)))

theorem h65535 : P.leaf 36 65535 = 10536895192 :=
  leaf_weighted (k := 26) (d := 10) (H := 65535) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 65535) (by decide) (by decide +kernel)) sum65535

theorem cover76983 : P.CoversSplit 26 10 76983 0x8000000000000000000000000000000000000000000000000000000000000000cc00cc0000000000cc00cc00000000000000000000000000000000000000000000000000000000000000000000000000000000000033003300000000003300330000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 587, 629, 636, 881, 972, 1315, 1658, 2008]) (by decide +kernel)

noncomputable def f76983 (i : ℕ) := rowWeight keep9 twice9 i * P.leaf 26 (78830592 + i)

theorem c76983_0 : rowSum f76983 0 1024 = 52390304 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 76983) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover76983 (by decide)
  decide +kernel

theorem sum76983 : rowSum f76983 0 1024 = 52390304 :=
  c76983_0

theorem h76983 : P.leaf 36 76983 = 52390304 :=
  leaf_weighted (k := 26) (d := 10) (H := 76983) (keep := keep9) (twice := twice9) rows (by decide) (by decide) bal9 (invRow9 (H := 76983) (by decide) (by decide +kernel)) sum76983

theorem cover76984 : P.CoversSplit 26 10 76984 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000021002100000000002100210000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 531, 538, 587, 629, 636, 881, 972, 1273, 1315, 1658]) (by decide +kernel)

noncomputable def f76984 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (78831616 + i)

theorem c76984_0 : rowSum f76984 0 1024 = 23983 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 76984) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover76984 (by decide)
  decide +kernel

theorem sum76984 : rowSum f76984 0 1024 = 23983 :=
  c76984_0

theorem h76984 : P.leaf 36 76984 = 23983 :=
  leaf_weighted (k := 26) (d := 10) (H := 76984) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 76984) (by decide) (by decide +kernel)) sum76984

theorem cover76985 : P.CoversSplit 26 10 76985 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000021002100000000002100210000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 531, 538, 587, 629, 636, 881, 972, 1315, 1658]) (by decide +kernel)

theorem c76985_0 : P.sumLeaves 26 78832640 1024 = 30223 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 76985) (lo := 0) (len := 1024) (W := 30223) check rows elimOK (by decide) (by decide) cover76985 (by decide)
  decide +kernel

theorem h76985 : P.leaf 36 76985 = 30223 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 30223)]) (.cons c76985_0 (.nil)) (by decide) (by decide))

theorem cover76987 : P.CoversSplit 26 10 76987 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000021002100000000002100210000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 531, 538, 587, 629, 636, 881, 972, 1315, 1658]) (by decide +kernel)

noncomputable def f76987 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (78834688 + i)

theorem c76987_0 : rowSum f76987 0 1024 = 43049 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 76987) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover76987 (by decide)
  decide +kernel

theorem sum76987 : rowSum f76987 0 1024 = 43049 :=
  c76987_0

theorem h76987 : P.leaf 36 76987 = 43049 :=
  leaf_weighted (k := 26) (d := 10) (H := 76987) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 76987) (by decide) (by decide +kernel)) sum76987

theorem cover76991 : P.CoversSplit 26 10 76991 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000021002100000000002100210000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 587, 629, 636, 881, 972, 1315, 1658]) (by decide +kernel)

noncomputable def f76991 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (78838784 + i)

theorem c76991_0 : rowSum f76991 0 1024 = 65523 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 76991) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover76991 (by decide)
  decide +kernel

theorem sum76991 : rowSum f76991 0 1024 = 65523 :=
  c76991_0

theorem h76991 : P.leaf 36 76991 = 65523 :=
  leaf_weighted (k := 26) (d := 10) (H := 76991) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 76991) (by decide) (by decide +kernel)) sum76991

theorem h77000 : P.leaf 36 77000 = 64 := by
  exact leaf_contract_factors (k := 36) (b := 6) (H := 77000) (ss := [(7, 1, 466), (8, 1, 472), (35, 1, 475), (37, 1, 482), (4, 1, 487), (2, 1, 411), (5, 1, 411), (3, 1, 417), (10, 1, 458), (11, 1, 459), (12, 1, 460), (14, 1, 465), (16, 1, 515), (17, 1, 516), (36, 1, 580), (6, 1, 433), (21, 1, 586), (29, 1, 587), (9, 1, 573), (28, 1, 629), (13, 1, 811), (18, 1, 860), (15, 1, 916), (31, 1, 930), (30, 1, 972), (19, 1, 1259), (33, 1, 1273), (32, 1, 1315), (20, 1, 1609), (34, 1, 1658)]) (ids := [20, 21, 22, 23, 24, 25]) (cs := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5, 6, 7, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [0, 6]) (W := 64) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem h77001 : P.leaf 36 77001 = 1024 := by
  exact leaf_contract_factors (k := 36) (b := 10) (H := 77001) (ss := [(35, 1, 475), (37, 1, 482), (4, 1, 487), (2, 1, 411), (5, 1, 411), (3, 1, 417), (36, 1, 580), (6, 1, 433), (21, 1, 586), (29, 1, 587), (9, 1, 573), (28, 1, 629), (13, 1, 867), (11, 1, 818), (12, 1, 825), (18, 1, 879), (15, 1, 916), (31, 1, 930), (30, 1, 972), (16, 1, 1210), (17, 1, 1217), (19, 1, 1259), (33, 1, 1273), (32, 1, 1315), (20, 1, 1609), (34, 1, 1658)]) (ids := [5, 6, 8, 12, 20, 21, 22, 23, 24, 25]) (cs := [1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 6, 7, 8, 9, 10, 11, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [0, 10]) (W := 1024) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem h77002 : P.leaf 36 77002 = 512 := by
  exact leaf_contract_factors (k := 36) (b := 9) (H := 77002) (ss := [(8, 1, 479), (37, 1, 482), (5, 1, 488), (3, 1, 417), (4, 1, 417), (16, 1, 515), (14, 1, 465), (17, 1, 516), (35, 1, 524), (36, 1, 580), (6, 1, 433), (21, 1, 586), (29, 1, 587), (9, 1, 573), (28, 1, 629), (18, 1, 860), (13, 1, 867), (12, 1, 825), (15, 1, 916), (31, 1, 930), (30, 1, 972), (19, 1, 1259), (33, 1, 1273), (10, 1, 811), (32, 1, 1315), (20, 1, 1609), (34, 1, 1658)]) (ids := [0, 5, 9, 20, 21, 22, 23, 24, 25]) (cs := [2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 6, 7, 8, 9, 10, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [0, 9]) (W := 512) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem h77003 : P.leaf 36 77003 = 4096 := by
  exact leaf_contract_factors (k := 36) (b := 12) (H := 77003) (ss := [(37, 1, 482), (5, 1, 488), (35, 1, 524), (4, 1, 536), (3, 1, 418), (36, 1, 580), (6, 1, 433), (21, 1, 586), (29, 1, 587), (9, 1, 573), (28, 1, 629), (13, 1, 867), (12, 1, 825), (18, 1, 880), (15, 1, 916), (31, 1, 930), (30, 1, 972), (16, 1, 1210), (17, 1, 1217), (19, 1, 1259), (33, 1, 1273), (32, 1, 1315), (20, 1, 1609), (34, 1, 1658)]) (ids := [0, 5, 6, 8, 9, 12, 20, 21, 22, 23, 24, 25]) (cs := [2, 1, 1, 1, 1, 3, 4, 1, 5, 6, 1, 1, 7, 1, 1, 1, 1, 1, 1, 1, 8, 9, 10, 11, 12, 13, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [0, 12]) (W := 4096) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem h77006 : P.leaf 36 77006 = 2352 := by
  exact leaf_contract_factors (k := 36) (b := 16) (H := 77006) (ss := [(35, 1, 524), (37, 1, 531), (4, 1, 536), (3, 1, 418), (5, 1, 418), (36, 1, 580), (21, 1, 586), (29, 1, 587), (9, 1, 573), (28, 1, 629), (13, 1, 867), (15, 1, 916), (31, 1, 930), (30, 1, 972), (19, 1, 1259), (33, 1, 1273), (10, 1, 811), (32, 1, 1315), (20, 1, 1609), (34, 1, 1658)]) (ids := [0, 4, 5, 6, 9, 10, 12, 14, 15, 16, 20, 21, 22, 23, 24, 25]) (cs := [2, 1, 1, 1, 3, 4, 5, 1, 1, 6, 7, 1, 8, 1, 9, 10, 11, 1, 1, 1, 12, 13, 14, 15, 16, 17, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [13, 3]) (W := 2352) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem h77007 : P.leaf 36 77007 = 25952 := by
  exact leaf_contract_factors (k := 36) (b := 18) (H := 77007) (ss := [(35, 1, 524), (37, 1, 531), (4, 1, 536), (5, 1, 537), (36, 1, 580), (21, 1, 586), (29, 1, 587), (9, 1, 573), (28, 1, 629), (13, 1, 867), (15, 1, 916), (31, 1, 930), (30, 1, 972), (19, 1, 1259), (33, 1, 1273), (32, 1, 1315), (20, 1, 1609), (34, 1, 1658)]) (ids := [0, 1, 4, 5, 6, 8, 9, 10, 12, 14, 15, 16, 20, 21, 22, 23, 24, 25]) (cs := [2, 3, 1, 1, 4, 5, 6, 1, 7, 8, 9, 1, 10, 1, 11, 12, 13, 1, 1, 1, 14, 15, 16, 17, 18, 19, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [15, 3]) (W := 25952) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem h77018 : P.leaf 36 77018 = 8192 := by
  exact leaf_contract_factors (k := 36) (b := 13) (H := 77018) (ss := [(37, 1, 482), (5, 1, 488), (36, 1, 580), (6, 1, 433), (21, 1, 586), (29, 1, 587), (9, 1, 573), (35, 1, 587), (28, 1, 629), (13, 1, 874), (12, 1, 825), (18, 1, 880), (15, 1, 916), (31, 1, 930), (14, 1, 860), (30, 1, 972), (17, 1, 1217), (19, 1, 1259), (33, 1, 1273), (10, 1, 811), (32, 1, 1315), (20, 1, 1609), (34, 1, 1658)]) (ids := [0, 1, 2, 5, 6, 9, 14, 20, 21, 22, 23, 24, 25]) (cs := [2, 3, 4, 1, 1, 5, 6, 1, 1, 7, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 9, 10, 11, 12, 13, 14, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [0, 13]) (W := 8192) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem h77019 : P.leaf 36 77019 = 32768 := by
  exact leaf_contract_factors (k := 36) (b := 15) (H := 77019) (ss := [(37, 1, 482), (5, 1, 488), (36, 1, 580), (6, 1, 433), (21, 1, 586), (29, 1, 587), (9, 1, 573), (35, 1, 587), (28, 1, 629), (13, 1, 874), (12, 1, 825), (18, 1, 880), (15, 1, 916), (31, 1, 930), (30, 1, 972), (17, 1, 1217), (19, 1, 1259), (33, 1, 1273), (32, 1, 1315), (20, 1, 1609), (34, 1, 1658)]) (ids := [0, 1, 2, 5, 6, 8, 9, 12, 14, 20, 21, 22, 23, 24, 25]) (cs := [2, 3, 4, 1, 1, 5, 6, 1, 7, 8, 1, 1, 9, 1, 10, 1, 1, 1, 1, 1, 11, 12, 13, 14, 15, 16, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [0, 15]) (W := 32768) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem h77020 : P.leaf 36 77020 = 6656 := by
  exact leaf_contract_factors (k := 36) (b := 13) (H := 77020) (ss := [(35, 1, 475), (4, 1, 487), (37, 1, 531), (5, 1, 537), (36, 1, 580), (21, 1, 586), (29, 1, 587), (9, 1, 573), (28, 1, 629), (13, 1, 874), (11, 1, 818), (18, 1, 879), (15, 1, 916), (31, 1, 930), (14, 1, 860), (30, 1, 972), (17, 1, 1217), (19, 1, 1259), (33, 1, 1273), (10, 1, 811), (32, 1, 1315), (20, 1, 1609), (34, 1, 1658)]) (ids := [0, 1, 4, 20, 5, 6, 10, 14, 21, 22, 23, 24, 25]) (cs := [2, 3, 1, 1, 4, 6, 7, 1, 1, 1, 8, 1, 1, 1, 9, 1, 1, 1, 1, 1, 5, 10, 11, 12, 13, 14, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [4, 9]) (W := 6656) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem h77021 : P.leaf 36 77021 = 24064 := by
  exact leaf_contract_factors (k := 36) (b := 15) (H := 77021) (ss := [(35, 1, 475), (4, 1, 487), (37, 1, 531), (5, 1, 537), (36, 1, 580), (21, 1, 586), (29, 1, 587), (9, 1, 573), (28, 1, 629), (13, 1, 874), (11, 1, 818), (18, 1, 879), (15, 1, 916), (31, 1, 930), (30, 1, 972), (17, 1, 1217), (19, 1, 1259), (33, 1, 1273), (32, 1, 1315), (20, 1, 1609), (34, 1, 1658)]) (ids := [0, 1, 4, 8, 12, 20, 5, 6, 10, 14, 21, 22, 23, 24, 25]) (cs := [2, 3, 1, 1, 4, 8, 9, 1, 5, 1, 10, 1, 6, 1, 11, 1, 1, 1, 1, 1, 7, 12, 13, 14, 15, 16, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [6, 9]) (W := 24064) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem h77022 : P.leaf 36 77022 = 21504 := by
  exact leaf_contract_factors (k := 36) (b := 18) (H := 77022) (ss := [(37, 1, 531), (5, 1, 537), (36, 1, 580), (21, 1, 586), (29, 1, 587), (9, 1, 573), (35, 1, 587), (28, 1, 629), (13, 1, 874), (15, 1, 916), (31, 1, 930), (30, 1, 972), (19, 1, 1259), (33, 1, 1273), (10, 1, 811), (32, 1, 1315), (20, 1, 1609), (34, 1, 1658)]) (ids := [0, 1, 2, 4, 5, 6, 9, 10, 12, 14, 15, 16, 20, 21, 22, 23, 24, 25]) (cs := [2, 3, 4, 1, 5, 6, 7, 1, 1, 8, 9, 1, 10, 1, 11, 12, 13, 1, 1, 1, 14, 15, 16, 17, 18, 19, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [15, 3]) (W := 21504) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem h77023 : P.leaf 36 77023 = 88256 := by
  exact leaf_contract_factors (k := 36) (b := 19) (H := 77023) (ss := [(37, 1, 531), (5, 1, 537), (36, 1, 580), (21, 1, 586), (29, 1, 587), (9, 1, 573), (35, 1, 587), (28, 1, 629), (13, 1, 874), (15, 1, 916), (31, 1, 930), (30, 1, 972), (19, 1, 1259), (33, 1, 1273), (32, 1, 1315), (20, 1, 1609), (34, 1, 1658)]) (ids := [0, 1, 2, 4, 5, 6, 8, 9, 10, 12, 14, 15, 16, 20, 21, 22, 23, 24, 25]) (cs := [2, 3, 4, 1, 5, 6, 7, 1, 8, 9, 10, 1, 11, 1, 12, 13, 14, 1, 1, 1, 15, 16, 17, 18, 19, 20, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [16, 3]) (W := 88256) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover77054 : P.CoversSplit 26 10 77054 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 580, 587, 629, 636, 881, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem c77054_0 : P.sumLeaves 26 78903296 1024 = 66376 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77054) (lo := 0) (len := 1024) (W := 66376) check rows elimOK (by decide) (by decide) cover77054 (by decide)
  decide +kernel

theorem h77054 : P.leaf 36 77054 = 66376 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 66376)]) (.cons c77054_0 (.nil)) (by decide) (by decide))

theorem cover77055 : P.CoversSplit 26 10 77055 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 580, 587, 629, 636, 881, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem c77055_0 : P.sumLeaves 26 78904320 1024 = 264640 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77055) (lo := 0) (len := 1024) (W := 264640) check rows elimOK (by decide) (by decide) cover77055 (by decide)
  decide +kernel

theorem h77055 : P.leaf 36 77055 = 264640 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 264640)]) (.cons c77055_0 (.nil)) (by decide) (by decide))

theorem cover77128 : P.CoversSplit 26 10 77128 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000500000000000000000000000000000000000000000500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 482, 530, 579, 629, 636, 972, 979, 1322, 1665]) (by decide +kernel)

theorem c77128_0 : P.sumLeaves 26 78979072 1024 = 23983 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77128) (lo := 0) (len := 1024) (W := 23983) check rows elimOK (by decide) (by decide) cover77128 (by decide)
  decide +kernel

theorem h77128 : P.leaf 36 77128 = 23983 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 23983)]) (.cons c77128_0 (.nil)) (by decide) (by decide))

theorem h77129 : P.leaf 36 77129 = 1024 := by
  exact leaf_contract_factors (k := 36) (b := 10) (H := 77129) (ss := [(28, 1, 474), (9, 1, 480), (37, 1, 482), (5, 1, 488), (20, 1, 572), (29, 1, 636), (13, 1, 867), (12, 1, 825), (36, 1, 874), (6, 1, 433), (30, 1, 481), (2, 1, 411), (3, 1, 418), (4, 1, 425), (15, 1, 473), (19, 1, 522), (32, 1, 530), (34, 1, 579), (18, 1, 879), (21, 1, 916), (31, 1, 979), (17, 1, 1217), (33, 1, 1322), (35, 1, 1665), (11, 1, 818), (16, 1, 1210)]) (ids := [5, 6, 8, 12, 20, 21, 22, 23, 24, 25]) (cs := [1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 6, 7, 8, 9, 10, 11, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [0, 10]) (W := 1024) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem h77131 : P.leaf 36 77131 = 8192 := by
  exact leaf_contract_factors (k := 36) (b := 13) (H := 77131) (ss := [(37, 1, 482), (5, 1, 488), (28, 1, 523), (29, 1, 636), (13, 1, 867), (12, 1, 825), (36, 1, 874), (6, 1, 433), (30, 1, 481), (2, 1, 411), (3, 1, 418), (4, 1, 425), (32, 1, 530), (34, 1, 579), (18, 1, 880), (21, 1, 929), (31, 1, 979), (17, 1, 1217), (33, 1, 1322), (19, 1, 1259), (20, 1, 1609), (35, 1, 1665), (16, 1, 1210)]) (ids := [5, 6, 7, 8, 9, 12, 13, 20, 21, 22, 23, 24, 25]) (cs := [1, 1, 1, 1, 1, 2, 3, 4, 5, 6, 1, 1, 7, 8, 1, 1, 1, 1, 1, 1, 9, 10, 11, 12, 13, 14, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [0, 13]) (W := 8192) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem h77132 : P.leaf 36 77132 = 848 := by
  exact leaf_contract_factors (k := 36) (b := 22) (H := 77132) (ss := [(9, 1, 466), (8, 1, 472), (37, 1, 531), (5, 1, 537), (17, 1, 516), (14, 1, 465), (20, 1, 572), (15, 1, 473), (18, 1, 860), (16, 1, 515), (21, 13, 867), (36, 13, 874), (13, 1, 825), (19, 1, 522)]) (ids := [0, 1, 2, 4, 5, 8, 9, 10, 20, 21, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 22, 23]) (cs := [2, 3, 4, 1, 5, 6, 1, 1, 7, 8, 9, 1, 1, 1, 1, 1, 1, 1, 1, 1, 10, 11, 22, 23, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 1, 1]) (bs := [20, 2]) (W := 848) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover77133 : P.CoversSplit 26 10 77133 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 579, 629, 636, 880, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c77133_0 : P.sumLeaves 26 78984192 1024 = 9656 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77133) (lo := 0) (len := 1024) (W := 9656) check rows elimOK (by decide) (by decide) cover77133 (by decide)
  decide +kernel

theorem h77133 : P.leaf 36 77133 = 9656 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 9656)]) (.cons c77133_0 (.nil)) (by decide) (by decide))

theorem cover77135 : P.CoversSplit 26 10 77135 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 579, 629, 636, 880, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c77135_0 : P.sumLeaves 26 78986240 1024 = 101656 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77135) (lo := 0) (len := 1024) (W := 101656) check rows elimOK (by decide) (by decide) cover77135 (by decide)
  decide +kernel

theorem h77135 : P.leaf 36 77135 = 101656 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 101656)]) (.cons c77135_0 (.nil)) (by decide) (by decide))

theorem cover77147 : P.CoversSplit 26 10 77147 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000500000000000000000000000000000000000000000500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 482, 530, 579, 629, 636, 972, 979, 1322, 1665]) (by decide +kernel)

theorem c77147_0 : P.sumLeaves 26 78998528 1024 = 68768 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77147) (lo := 0) (len := 1024) (W := 68768) check rows elimOK (by decide) (by decide) cover77147 (by decide)
  decide +kernel

theorem h77147 : P.leaf 36 77147 = 68768 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 68768)]) (.cons c77147_0 (.nil)) (by decide) (by decide))

theorem cover77148 : P.CoversSplit 26 10 77148 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 880, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c77148_0 : P.sumLeaves 26 78999552 1024 = 13120 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77148) (lo := 0) (len := 1024) (W := 13120) check rows elimOK (by decide) (by decide) cover77148 (by decide)
  decide +kernel

theorem h77148 : P.leaf 36 77148 = 13120 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 13120)]) (.cons c77148_0 (.nil)) (by decide) (by decide))

theorem cover77149 : P.CoversSplit 26 10 77149 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 579, 629, 636, 880, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c77149_0 : P.sumLeaves 26 79000576 1024 = 96184 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77149) (lo := 0) (len := 1024) (W := 96184) check rows elimOK (by decide) (by decide) cover77149 (by decide)
  decide +kernel

theorem h77149 : P.leaf 36 77149 = 96184 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 96184)]) (.cons c77149_0 (.nil)) (by decide) (by decide))

theorem cover77151 : P.CoversSplit 26 10 77151 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 880, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c77151_0 : P.sumLeaves 26 79002624 1024 = 630212 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77151) (lo := 0) (len := 1024) (W := 630212) check rows elimOK (by decide) (by decide) cover77151 (by decide)
  decide +kernel

theorem h77151 : P.leaf 36 77151 = 630212 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 630212)]) (.cons c77151_0 (.nil)) (by decide) (by decide))

theorem cover77164 : P.CoversSplit 26 10 77164 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c77164_0 : P.sumLeaves 26 79015936 1024 = 6784 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77164) (lo := 0) (len := 1024) (W := 6784) check rows elimOK (by decide) (by decide) cover77164 (by decide)
  decide +kernel

theorem h77164 : P.leaf 36 77164 = 6784 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6784)]) (.cons c77164_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(65527, 60), (65535, 15), (76983, 6), (76984, 60), (76985, 180), (76987, 180), (76991, 60), (77000, 180), (77001, 180), (77002, 720), (77003, 720), (77006, 360), (77007, 360), (77018, 360), (77019, 360), (77020, 360), (77021, 360), (77022, 720), (77023, 720), (77054, 180), (77055, 180), (77128, 60), (77129, 360), (77131, 360), (77132, 360), (77133, 720), (77135, 360), (77147, 120), (77148, 360), (77149, 720), (77151, 360), (77164, 360)]

theorem segOK : checkSeg 20 perms 65527 77165 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 65527 77165 10461 396514203684 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 396514203684)
    (SegSum.cons (w := 60) h65527 (SegSum.cons (w := 15) h65535 (SegSum.cons (w := 6) h76983 (SegSum.cons (w := 60) h76984 (SegSum.cons (w := 180) h76985 (SegSum.cons (w := 180) h76987 (SegSum.cons (w := 60) h76991 (SegSum.cons (w := 180) h77000 (SegSum.cons (w := 180) h77001 (SegSum.cons (w := 720) h77002 (SegSum.cons (w := 720) h77003 (SegSum.cons (w := 360) h77006 (SegSum.cons (w := 360) h77007 (SegSum.cons (w := 360) h77018 (SegSum.cons (w := 360) h77019 (SegSum.cons (w := 360) h77020 (SegSum.cons (w := 360) h77021 (SegSum.cons (w := 720) h77022 (SegSum.cons (w := 720) h77023 (SegSum.cons (w := 180) h77054 (SegSum.cons (w := 180) h77055 (SegSum.cons (w := 60) h77128 (SegSum.cons (w := 360) h77129 (SegSum.cons (w := 360) h77131 (SegSum.cons (w := 360) h77132 (SegSum.cons (w := 720) h77133 (SegSum.cons (w := 360) h77135 (SegSum.cons (w := 120) h77147 (SegSum.cons (w := 360) h77148 (SegSum.cons (w := 720) h77149 (SegSum.cons (w := 360) h77151 (SegSum.cons (w := 360) h77164 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S39
