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

namespace RACert.S6N0.C0.S58

open RACert RACert.Problem

theorem cover113143 : P.CoversSplit 26 10 113143 0xcc00cc00cc00c800cc00cc00cc00c80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 629, 636, 930, 1266, 1315]) (by decide +kernel)

theorem h113143 : P.leaf 36 113143 = 137029062 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 113143) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 113143) (weight := fun _ => 1) (xs := [907, 910, 911, 922, 923, 926, 927, 938, 939, 942, 943, 954, 955, 958, 959, 971, 974, 975, 986, 987, 990, 991, 1002, 1003, 1006, 1007, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover113143 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h90039 : P.leaf 36 90039 = 137029062 :=
  orient72 (v := 113143) (by decide) (by decide +kernel) h113143

theorem cover831711 : P.CoversSplit 26 10 831711 0x888800008888000088880000888800000000000000000000000000000000000088880000888800008c8c00008c8c0000000000000000000000000000000000008888000088aa00008888000088aa0000000000000000000000000000000000008888000088aa00008c8c00008caf000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 587, 629, 636, 867, 872]) (by decide +kernel)

noncomputable def f831711 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 26 (851672064 + i)

theorem c831711_0 : rowSum f831711 0 1024 = 37658492 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 831711) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover831711 (by decide)
  decide +kernel

theorem sum831711 : rowSum f831711 0 1024 = 37658492 :=
  c831711_0

theorem h831711 : P.leaf 36 831711 = 37658492 :=
  leaf_weighted (k := 26) (d := 10) (H := 831711) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 831711) (by decide) (by decide +kernel)) sum831711

theorem h90042 : P.leaf 36 90042 = 37658492 :=
  orient324 (v := 831711) (by decide) (by decide +kernel) h831711

theorem cover90043 : P.CoversSplit 26 10 90043 0xf0f0f0f000000000f0f0f0f500000000f0f0f0f000000030f0f0f0f000000000000000000000000000005050000000000000000000000000000050500000000000000000000000000000000000000000003000300000000000300030000000000000000000000000000000000000000000000000000000000000001000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 972, 979, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f90043 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (92204032 + i)

theorem c90043_0 : rowSum f90043 0 1024 = 169648438 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 90043) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover90043 (by decide)
  decide +kernel

theorem sum90043 : rowSum f90043 0 1024 = 169648438 :=
  c90043_0

theorem h90043 : P.leaf 36 90043 = 169648438 :=
  leaf_weighted (k := 26) (d := 10) (H := 90043) (keep := keep4) (twice := twice4) rows (by decide) (by decide) (bal4) (invRow4 (H := 90043) (by decide) (by decide +kernel)) sum90043

theorem cover113146 : P.CoversSplit 26 10 113146 0xaaaaaaaaaaaaaaaaaaaaababaaaaaaaa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002200220000000000220022000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 531, 629, 636, 867, 1266, 1315, 1665]) (by decide +kernel)

theorem c113146_0 : P.sumLeaves 26 115861504 1024 = 160784006 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 113146) (lo := 0) (len := 1024) (W := 160784006) check rows elimOK (by decide) (by decide) cover113146 (by decide)
  decide +kernel

theorem h113146 : P.leaf 36 113146 = 160784006 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 160784006)]) (.cons c113146_0 (.nil)) (by decide) (by decide))

theorem h90044 : P.leaf 36 90044 = 160784006 :=
  orient72 (v := 113146) (by decide) (by decide +kernel) h113146

theorem cover113150 : P.CoversSplit 26 10 113150 0xfffffffffffffafafffffefefffffafa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003300320000000000330032000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [531, 629, 636, 867, 1266, 1315, 1665]) (by decide +kernel)

theorem c113150_0 : P.sumLeaves 26 115865600 988 = 266816104 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 113150) (lo := 0) (len := 988) (W := 266816104) check rows elimOK (by decide) (by decide) cover113150 (by decide)
  decide +kernel

theorem c113150_1 : P.sumLeaves 26 115866588 36 = 210112836 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 113150) (lo := 988) (len := 36) (W := 210112836) check rows elimOK (by decide) (by decide) cover113150 (by decide)
  decide +kernel

theorem h113150 : P.leaf 36 113150 = 476928940 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(988, 266816104), (36, 210112836)]) (.cons c113150_0 (.cons c113150_1 (.nil))) (by decide) (by decide))

theorem h90045 : P.leaf 36 90045 = 476928940 :=
  orient72 (v := 113150) (by decide) (by decide +kernel) h113150

theorem cover113147 : P.CoversSplit 26 10 113147 0xaaaaaaaaaaaaaaaaaaaaababaaaaaaaa00000000000000000000000000220000000000000000000000000000000000000000000000000000000000000000000000000000002200220000000000220022000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 629, 636, 930, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c113147_0 : P.sumLeaves 26 115862528 1024 = 306219200 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 113147) (lo := 0) (len := 1024) (W := 306219200) check rows elimOK (by decide) (by decide) cover113147 (by decide)
  decide +kernel

theorem h113147 : P.leaf 36 113147 = 306219200 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 306219200)]) (.cons c113147_0 (.nil)) (by decide) (by decide))

theorem h90046 : P.leaf 36 90046 = 306219200 :=
  orient72 (v := 113147) (by decide) (by decide +kernel) h113147

theorem cover113151 : P.CoversSplit 26 10 113151 0xfffffffffffffafafffffefefffffafa00000000000000000000000000220000000000000000000000000000000000000000000000000000000000000000000000000000003300320000000000330032000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [629, 636, 930, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c113151_0 : P.sumLeaves 26 115866624 986 = 471711124 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 113151) (lo := 0) (len := 986) (W := 471711124) check rows elimOK (by decide) (by decide) cover113151 (by decide)
  decide +kernel

theorem c113151_1 : P.sumLeaves 26 115867610 38 = 288940516 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 113151) (lo := 986) (len := 38) (W := 288940516) check rows elimOK (by decide) (by decide) cover113151 (by decide)
  decide +kernel

theorem h113151 : P.leaf 36 113151 = 760651640 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(986, 471711124), (38, 288940516)]) (.cons c113151_0 (.cons c113151_1 (.nil))) (by decide) (by decide))

theorem h90047 : P.leaf 36 90047 = 760651640 :=
  orient72 (v := 113151) (by decide) (by decide +kernel) h113151

theorem cover831795 : P.CoversSplit 26 10 831795 0x8000800000000000000000000000000080008000000000000000000000000000800080000000000000000800000000008000800000000000000008000000000080008000000000000000000000000000800080000080008000000000000000008000800000000000000008000000000080008000008000800000080000000008 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 538, 579, 629, 636]) (by decide +kernel)

theorem h831795 : P.leaf 36 831795 = 1735428 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 831795) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 831795) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 831795) (weight := rowWeight keep2 twice2) (xs := [3, 43, 71, 87, 111, 127, 171, 239, 255, 327, 343, 367, 383, 495, 511, 555, 623, 639, 683, 751, 767, 879, 895, 1007, 1023]) check rows elimOK (by decide) (by decide) cover831795 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h90052 : P.leaf 36 90052 = 1735428 :=
  orient324 (v := 831795) (by decide) (by decide +kernel) h831795

theorem cover90053 : P.CoversSplit 26 10 90053 0xff000000ff030501ff000000ff030500ff000000ff030500fa000000c8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 922, 923, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f90053 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (92214272 + i)

theorem c90053_0 : rowSum f90053 0 1024 = 90399838 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 90053) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover90053 (by decide)
  decide +kernel

theorem sum90053 : rowSum f90053 0 1024 = 90399838 :=
  c90053_0

theorem h90053 : P.leaf 36 90053 = 90399838 :=
  leaf_weighted (k := 26) (d := 10) (H := 90053) (keep := keep4) (twice := twice4) rows (by decide) (by decide) (bal4) (invRow4 (H := 90053) (by decide) (by decide +kernel)) sum90053

theorem cover604526 : P.CoversSplit 26 10 604526 0xaa00aa0000000000aa00ab0000000000aa00aa0000000002aa00ab0000000002000000000000000000000a0000000000000000000000000000000a000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [531, 579, 629, 636, 930, 972, 979, 1273, 1315, 1322]) (by decide +kernel)

theorem c604526_0 : P.sumLeaves 26 619034624 1024 = 13606316 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 604526) (lo := 0) (len := 1024) (W := 13606316) check rows elimOK (by decide) (by decide) cover604526 (by decide)
  decide +kernel

theorem h604526 : P.leaf 36 604526 = 13606316 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 13606316)]) (.cons c604526_0 (.nil)) (by decide) (by decide))

theorem h90054 : P.leaf 36 90054 = 13606316 :=
  orient325 (v := 604526) (by decide) (by decide +kernel) h604526

theorem cover90055 : P.CoversSplit 26 10 90055 0xff000000ff030501ff000000ff030500ff000000ff030500fa000000c8000000000000000000000000000000000000000000000000000000000000000000000000000000333301010000000033330100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c90055_0 : P.sumLeaves 26 92216320 1024 = 162593629 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90055) (lo := 0) (len := 1024) (W := 162593629) check rows elimOK (by decide) (by decide) cover90055 (by decide)
  decide +kernel

theorem h90055 : P.leaf 36 90055 = 162593629 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 162593629)]) (.cons c90055_0 (.nil)) (by decide) (by decide))

theorem cover306650 : P.CoversSplit 26 10 306650 0xaaaa0000aaaa0000aaaa0000aaaa000000000000000000000000000000000000000000000000000000000a0000000a000000000000000000000000000000000000220000002200000022000000220000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [481, 530, 629, 636, 881, 1272, 1665]) (ps := [(3, [486, 510], [530])]) (by decide +kernel)

theorem c306650_0 : P.sumLeaves 26 314009600 1024 = 33183024 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 306650) (lo := 0) (len := 1024) (W := 33183024) check rows elimOK (by decide) (by decide) cover306650 (by decide)
  decide +kernel

theorem h306650 : P.leaf 36 306650 = 33183024 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 33183024)]) (.cons c306650_0 (.nil)) (by decide) (by decide))

theorem h90060 : P.leaf 36 90060 = 33183024 :=
  orient74 (v := 306650) (by decide) (by decide +kernel) h306650

theorem cover90061 : P.CoversSplit 26 10 90061 0xffff0000fffc0504ffff0000fffc0500ffff0000fffc0500fafa0000c8c80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 922, 923, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c90061_0 : P.sumLeaves 26 92222464 989 = 157489055 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90061) (lo := 0) (len := 989) (W := 157489055) check rows elimOK (by decide) (by decide) cover90061 (by decide)
  decide +kernel

theorem c90061_1 : P.sumLeaves 26 92223453 35 = 85286112 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90061) (lo := 989) (len := 35) (W := 85286112) check rows elimOK (by decide) (by decide) cover90061 (by decide)
  decide +kernel

theorem h90061 : P.leaf 36 90061 = 242775167 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(989, 157489055), (35, 85286112)]) (.cons c90061_0 (.cons c90061_1 (.nil))) (by decide) (by decide))

theorem cover306651 : P.CoversSplit 26 10 306651 0xaaaa0000aaaa0000aaaa0000aaaa000000000000000000000000000000000000000000000000000000000a0a00000a0a0000000000000000000000000000000000220000002200000022000000220000000000000000000000000000000000000000000000000000000000020000000200000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 629, 636, 1272, 1665]) (by decide +kernel)

theorem c306651_0 : P.sumLeaves 26 314010624 1024 = 96819189 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 306651) (lo := 0) (len := 1024) (W := 96819189) check rows elimOK (by decide) (by decide) cover306651 (by decide)
  decide +kernel

theorem h306651 : P.leaf 36 306651 = 96819189 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 96819189)]) (.cons c306651_0 (.nil)) (by decide) (by decide))

theorem h90062 : P.leaf 36 90062 = 96819189 :=
  orient74 (v := 306651) (by decide) (by decide +kernel) h306651

theorem cover90063 : P.CoversSplit 26 10 90063 0xffff0000fffc0504ffff0000fffc0500ffff0000fffc0500fafa0000c8c800000000000000000000000000000000000000000000000000000000000000000000ffff0000ffcc0504ffff0000ffcc0500ffff0000cc000400fafa0000c80000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c90063_0 : P.sumLeaves 26 92224512 511 = 139006792 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90063) (lo := 0) (len := 511) (W := 139006792) check rows elimOK (by decide) (by decide) cover90063 (by decide)
  decide +kernel

theorem c90063_1 : P.sumLeaves 26 92225023 477 = 303181552 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90063) (lo := 511) (len := 477) (W := 303181552) check rows elimOK (by decide) (by decide) cover90063 (by decide)
  decide +kernel

theorem c90063_2 : P.sumLeaves 26 92225500 36 = 132750948 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90063) (lo := 988) (len := 36) (W := 132750948) check rows elimOK (by decide) (by decide) cover90063 (by decide)
  decide +kernel

theorem h90063 : P.leaf 36 90063 = 574939292 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(511, 139006792), (477, 303181552), (36, 132750948)]) (.cons c90063_0 (.cons c90063_1 (.cons c90063_2 (.nil)))) (by decide) (by decide))

theorem cover90070 : P.CoversSplit 26 10 90070 0xff000000ff030501ff000000ff030500ff000000ff030500fa000000c8000000050005000501050100000000000000000500050005010500000000000000000000000000333301010000000033330100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f90070 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (92231680 + i)

theorem c90070_0 : rowSum f90070 0 1024 = 136726445 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 90070) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover90070 (by decide)
  decide +kernel

theorem sum90070 : rowSum f90070 0 1024 = 136726445 :=
  c90070_0

theorem h90070 : P.leaf 36 90070 = 136726445 :=
  leaf_weighted (k := 26) (d := 10) (H := 90070) (keep := keep4) (twice := twice4) rows (by decide) (by decide) (bal4) (invRow4 (H := 90070) (by decide) (by decide +kernel)) sum90070

theorem cover90071 : P.CoversSplit 26 10 90071 0xff000000ff030501ff000000ff030500ff000000ff030500fa000000c8000000050005000501050100000000000000000500050005010500000000000000000000000000333301010000000033330100000000000000000000000000000000000000000001010101000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f90071 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (92232704 + i)

theorem c90071_0 : rowSum f90071 0 1024 = 268401241 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 90071) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover90071 (by decide)
  decide +kernel

theorem sum90071 : rowSum f90071 0 1024 = 268401241 :=
  c90071_0

theorem h90071 : P.leaf 36 90071 = 268401241 :=
  leaf_weighted (k := 26) (d := 10) (H := 90071) (keep := keep4) (twice := twice4) rows (by decide) (by decide) (bal4) (invRow4 (H := 90071) (by decide) (by decide +kernel)) sum90071

theorem cover90076 : P.CoversSplit 26 10 90076 0xffff0000fffc0504ffff0000fffc0500ffff0000fffc0500fafa0000c8c80000050505050504050400000000000000000505050505040500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 874, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c90076_0 : P.sumLeaves 26 92237824 947 = 79654741 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90076) (lo := 0) (len := 947) (W := 79654741) check rows elimOK (by decide) (by decide) cover90076 (by decide)
  decide +kernel

theorem c90076_1 : P.sumLeaves 26 92238771 77 = 142416210 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90076) (lo := 947) (len := 77) (W := 142416210) check rows elimOK (by decide) (by decide) cover90076 (by decide)
  decide +kernel

theorem h90076 : P.leaf 36 90076 = 222070951 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(947, 79654741), (77, 142416210)]) (.cons c90076_0 (.cons c90076_1 (.nil))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(90039, 720), (90042, 360), (90043, 360), (90044, 720), (90045, 720), (90046, 720), (90047, 720), (90052, 360), (90053, 360), (90054, 720), (90055, 720), (90060, 720), (90061, 720), (90062, 720), (90063, 720), (90070, 360), (90071, 360), (90076, 720)]

theorem segOK : checkSeg 20 perms 90039 90077 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 90039 90077 10800 2548717457040 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 2548717457040)
    (SegSum.cons (w := 720) h90039 (SegSum.cons (w := 360) h90042 (SegSum.cons (w := 360) h90043 (SegSum.cons (w := 720) h90044 (SegSum.cons (w := 720) h90045 (SegSum.cons (w := 720) h90046 (SegSum.cons (w := 720) h90047 (SegSum.cons (w := 360) h90052 (SegSum.cons (w := 360) h90053 (SegSum.cons (w := 720) h90054 (SegSum.cons (w := 720) h90055 (SegSum.cons (w := 720) h90060 (SegSum.cons (w := 720) h90061 (SegSum.cons (w := 720) h90062 (SegSum.cons (w := 720) h90063 (SegSum.cons (w := 360) h90070 (SegSum.cons (w := 360) h90071 (SegSum.cons (w := 720) h90076 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S58
