/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S6N0.C0.Defs

/-! Generated certificate for the identity on six symmetric diversity atoms. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S6N0.C0.S33

open RACert RACert.Problem

theorem cover16246 : P.CoversSplit 26 10 16246 0xff00ff00ff00fa00000000000000000000000000000000000000000000000000550050005500500055005000550050000000000000000000000000000000000000000000000000000000000000000000000000003300320000000000110010000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 880, 930, 972, 979, 1265, 1315, 1658]) (by decide +kernel)

theorem c16246_0 : P.sumLeaves 26 16635904 1024 = 20125516 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16246) (lo := 0) (len := 1024) (W := 20125516) check rows elimOK (by decide) (by decide) cover16246 (by decide)
  decide +kernel

theorem h16246 : P.leaf 36 16246 = 20125516 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 20125516)]) (.cons c16246_0 (.nil)) (by decide) (by decide))

theorem cover16247 : P.CoversSplit 26 10 16247 0xff00ff00ff00fa00000000000000000000000000000000000000000000000000550050005500500055005000550050000000000000000000000000000000000000000000000000000000000000000000000000003300320000000000110010000000000000000000000000000000000000000000110010000000000011001000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 930, 972, 979, 1265, 1315, 1658]) (by decide +kernel)

theorem c16247_0 : P.sumLeaves 26 16636928 1024 = 54999608 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16247) (lo := 0) (len := 1024) (W := 54999608) check rows elimOK (by decide) (by decide) cover16247 (by decide)
  decide +kernel

theorem h16247 : P.leaf 36 16247 = 54999608 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 54999608)]) (.cons c16247_0 (.nil)) (by decide) (by decide))

theorem cover16248 : P.CoversSplit 26 10 16248 0xa0a0a0a0a0a0a0800000000000000000a0a0a0a0a080a08000000000000000000000505000005040000050500000504000005050000050400000500000005000a0a0a0a0a080a0800000000000000000a000a000a000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 579, 874, 930, 972, 1273, 1322, 1665]) (by decide +kernel)

theorem c16248_0 : P.sumLeaves 26 16637952 1024 = 791920 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16248) (lo := 0) (len := 1024) (W := 791920) check rows elimOK (by decide) (by decide) cover16248 (by decide)
  decide +kernel

theorem h16248 : P.leaf 36 16248 = 791920 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 791920)]) (.cons c16248_0 (.nil)) (by decide) (by decide))

theorem cover16249 : P.CoversSplit 26 10 16249 0xa0a0a0a0a0a0a0800000000000000000a0a0a0a0a080a08000000000000000000000505000005040000050500000504000005050000050400000500000005000a0a0a0a0a080a0800000000000000000a000a000a000a00000000000000000000000505000005040000050500000504000005000000050000000500000005000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 579, 930, 972, 1273, 1322, 1665]) (by decide +kernel)

theorem c16249_0 : P.sumLeaves 26 16638976 1021 = 3229912 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16249) (lo := 0) (len := 1021) (W := 3229912) check rows elimOK (by decide) (by decide) cover16249 (by decide)
  decide +kernel

theorem c16249_1 : P.sumLeaves 26 16639997 3 = 349696 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16249) (lo := 1021) (len := 3) (W := 349696) check rows elimOK (by decide) (by decide) cover16249 (by decide)
  decide +kernel

theorem h16249 : P.leaf 36 16249 = 3579608 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1021, 3229912), (3, 349696)]) (.cons c16249_0 (.cons c16249_1 (.nil))) (by decide) (by decide))

theorem cover16250 : P.CoversSplit 26 10 16250 0xa0a0a0a0a0a0a0800000000000000000a0a0a0a0a080a08000000000000000000000000000000000000000000000000000000000000000000000000000000000a0a0a0a0a080a0800000000000000000a000a000a000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 579, 874, 930, 972, 979, 1273, 1315, 1322, 1665]) (by decide +kernel)

theorem c16250_0 : P.sumLeaves 26 16640000 1024 = 14342524 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16250) (lo := 0) (len := 1024) (W := 14342524) check rows elimOK (by decide) (by decide) cover16250 (by decide)
  decide +kernel

theorem h16250 : P.leaf 36 16250 = 14342524 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 14342524)]) (.cons c16250_0 (.nil)) (by decide) (by decide))

theorem cover16251 : P.CoversSplit 26 10 16251 0xa0a0a0a0a0a0a0800000000000000000a0a0a0a0a080a08000000000000000000000000000000000000000000000000000000000000000000000000000000000a0a0a0a0a080a0800000000000000000a000a000a000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 579, 930, 972, 979, 1273, 1315, 1322, 1665]) (by decide +kernel)

theorem c16251_0 : P.sumLeaves 26 16641024 1024 = 28362824 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16251) (lo := 0) (len := 1024) (W := 28362824) check rows elimOK (by decide) (by decide) cover16251 (by decide)
  decide +kernel

theorem h16251 : P.leaf 36 16251 = 28362824 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 28362824)]) (.cons c16251_0 (.nil)) (by decide) (by decide))

theorem cover16254 : P.CoversSplit 26 10 16254 0xfffffffafffffac80000000000000000fffffffaffccfac855005000550050005555505055555040555550505555504055555050554450405500500055005000fffffffaffccfac80000000000000000ff00ff00ff00fa0055005000550050000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 874, 930, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c16254_0 : P.sumLeaves 26 16644096 538 = 26544622 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16254) (lo := 0) (len := 538) (W := 26544622) check rows elimOK (by decide) (by decide) cover16254 (by decide)
  decide +kernel

theorem c16254_1 : P.sumLeaves 26 16644634 309 = 18695586 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16254) (lo := 538) (len := 309) (W := 18695586) check rows elimOK (by decide) (by decide) cover16254 (by decide)
  decide +kernel

theorem c16254_2 : P.sumLeaves 26 16644943 175 = 61045964 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16254) (lo := 847) (len := 175) (W := 61045964) check rows elimOK (by decide) (by decide) cover16254 (by decide)
  decide +kernel

theorem c16254_3 : P.sumLeaves 26 16645118 2 = 4240804 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16254) (lo := 1022) (len := 2) (W := 4240804) check rows elimOK (by decide) (by decide) cover16254 (by decide)
  decide +kernel

theorem h16254 : P.leaf 36 16254 = 110526976 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(538, 26544622), (309, 18695586), (175, 61045964), (2, 4240804)]) (.cons c16254_0 (.cons c16254_1 (.cons c16254_2 (.cons c16254_3 (.nil))))) (by decide) (by decide))

theorem cover16255 : P.CoversSplit 26 10 16255 0xfffffffafffffac80000000000000000fffffffaffccfac855005000550050005555505055555040555550505555504055555050554450405500500055005000fffffffaffccfac80000000000000000ff00ff00ff00fa0055005000550050005555505055445040555550505544504055005000550050005500500055005000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 930, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c16255_0 : P.sumLeaves 26 16645120 364 = 8079932 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16255) (lo := 0) (len := 364) (W := 8079932) check rows elimOK (by decide) (by decide) cover16255 (by decide)
  decide +kernel

theorem c16255_1 : P.sumLeaves 26 16645484 282 = 44533504 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16255) (lo := 364) (len := 282) (W := 44533504) check rows elimOK (by decide) (by decide) cover16255 (by decide)
  decide +kernel

theorem c16255_2 : P.sumLeaves 26 16645766 237 = 53141143 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16255) (lo := 646) (len := 237) (W := 53141143) check rows elimOK (by decide) (by decide) cover16255 (by decide)
  decide +kernel

theorem c16255_3 : P.sumLeaves 26 16646003 141 = 111000533 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16255) (lo := 883) (len := 141) (W := 111000533) check rows elimOK (by decide) (by decide) cover16255 (by decide)
  decide +kernel

theorem h16255 : P.leaf 36 16255 = 216755112 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(364, 8079932), (282, 44533504), (237, 53141143), (141, 111000533)]) (.cons c16255_0 (.cons c16255_1 (.cons c16255_2 (.cons c16255_3 (.nil))))) (by decide) (by decide))

theorem cover16304 : P.CoversSplit 26 10 16304 0xc000c00000000000c000c00000000000000000000000000000000000000000000000c0000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 930, 972, 979, 1273, 1315, 1658, 1665]) (by decide +kernel)

theorem c16304_0 : P.sumLeaves 26 16695296 1024 = 27000 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16304) (lo := 0) (len := 1024) (W := 27000) check rows elimOK (by decide) (by decide) cover16304 (by decide)
  decide +kernel

theorem h16304 : P.leaf 36 16304 = 27000 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 27000)]) (.cons c16304_0 (.nil)) (by decide) (by decide))

theorem cover16305 : P.CoversSplit 26 10 16305 0xc000c00000000000c000c00000000000000000000000000000000000000000000000c0000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 538, 930, 972, 979, 1273, 1315, 1658, 1665]) (by decide +kernel)

theorem c16305_0 : P.sumLeaves 26 16696320 1024 = 1614808 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16305) (lo := 0) (len := 1024) (W := 1614808) check rows elimOK (by decide) (by decide) cover16305 (by decide)
  decide +kernel

theorem h16305 : P.leaf 36 16305 = 1614808 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1614808)]) (.cons c16305_0 (.nil)) (by decide) (by decide))

theorem cover16306 : P.CoversSplit 26 10 16306 0xc000c00000000000c000c00000000000000000000000000000000000000000000000c0000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 538, 930, 972, 979, 1273, 1315, 1658, 1665]) (by decide +kernel)

theorem c16306_0 : P.sumLeaves 26 16697344 1024 = 1251056 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16306) (lo := 0) (len := 1024) (W := 1251056) check rows elimOK (by decide) (by decide) cover16306 (by decide)
  decide +kernel

theorem h16306 : P.leaf 36 16306 = 1251056 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1251056)]) (.cons c16306_0 (.nil)) (by decide) (by decide))

theorem cover16307 : P.CoversSplit 26 10 16307 0xc000c00000000000c000c00000000000000000000000000000000000000000000000c0000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 538, 930, 972, 979, 1315, 1658, 1665]) (by decide +kernel)

theorem c16307_0 : P.sumLeaves 26 16698368 1024 = 5725552 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16307) (lo := 0) (len := 1024) (W := 5725552) check rows elimOK (by decide) (by decide) cover16307 (by decide)
  decide +kernel

theorem h16307 : P.leaf 36 16307 = 5725552 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5725552)]) (.cons c16307_0 (.nil)) (by decide) (by decide))

theorem cover16310 : P.CoversSplit 26 10 16310 0xcc00cc0000000000cc00c8000000000000000000000000000000000000000000cc00c0000000000088008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 930, 972, 979, 1265, 1273, 1658, 1665]) (by decide +kernel)

theorem c16310_0 : P.sumLeaves 26 16701440 1024 = 8893248 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16310) (lo := 0) (len := 1024) (W := 8893248) check rows elimOK (by decide) (by decide) cover16310 (by decide)
  decide +kernel

theorem h16310 : P.leaf 36 16310 = 8893248 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8893248)]) (.cons c16310_0 (.nil)) (by decide) (by decide))

theorem cover16311 : P.CoversSplit 26 10 16311 0xcc00cc0000000000cc00c8000000000000000000000000000000000000000000cc00c0000000000088008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 930, 972, 979, 1265, 1658, 1665]) (by decide +kernel)

theorem c16311_0 : P.sumLeaves 26 16702464 1024 = 39549324 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16311) (lo := 0) (len := 1024) (W := 39549324) check rows elimOK (by decide) (by decide) cover16311 (by decide)
  decide +kernel

theorem h16311 : P.leaf 36 16311 = 39549324 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 39549324)]) (.cons c16311_0 (.nil)) (by decide) (by decide))

theorem cover16312 : P.CoversSplit 26 10 16312 0xf0f0f0f500000030f0f0f0f00000003000300031000000300000000000000000000000000000000000000000000000000000000000000000000000000000000000300031003000300030003000300030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 874, 923, 930, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c16312_0 : P.sumLeaves 26 16703488 1024 = 820476 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16312) (lo := 0) (len := 1024) (W := 820476) check rows elimOK (by decide) (by decide) cover16312 (by decide)
  decide +kernel

theorem h16312 : P.leaf 36 16312 = 820476 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 820476)]) (.cons c16312_0 (.nil)) (by decide) (by decide))

theorem cover16313 : P.CoversSplit 26 10 16313 0xf0f0f0f500000030f0f0f0f00000003000300031000000300000000000000000000000000000000000000000000000000000000000000000000000000000000000300031003000300030003000300030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 923, 930, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c16313_0 : P.sumLeaves 26 16704512 1024 = 25417970 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16313) (lo := 0) (len := 1024) (W := 25417970) check rows elimOK (by decide) (by decide) cover16313 (by decide)
  decide +kernel

theorem h16313 : P.leaf 36 16313 = 25417970 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 25417970)]) (.cons c16313_0 (.nil)) (by decide) (by decide))

theorem cover16314 : P.CoversSplit 26 10 16314 0xf0f0f0f500000030f0f0f0f00000003000300031000000300000000000000000000050500000001000000000000000000000001000000010000000000000000000300031003000300030003000300030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 874, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c16314_0 : P.sumLeaves 26 16705536 1024 = 19444986 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16314) (lo := 0) (len := 1024) (W := 19444986) check rows elimOK (by decide) (by decide) cover16314 (by decide)
  decide +kernel

theorem h16314 : P.leaf 36 16314 = 19444986 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 19444986)]) (.cons c16314_0 (.nil)) (by decide) (by decide))

theorem cover16315 : P.CoversSplit 26 10 16315 0xf0f0f0f500000030f0f0f0f00000003000300031000000300000000000000000000050500000001000000000000000000000001000000010000000000000000000300031003000300030003000300030000000000000000000000000000000000000001000000010000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c16315_0 : P.sumLeaves 26 16706560 1024 = 67496199 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16315) (lo := 0) (len := 1024) (W := 67496199) check rows elimOK (by decide) (by decide) cover16315 (by decide)
  decide +kernel

theorem h16315 : P.leaf 36 16315 = 67496199 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 67496199)]) (.cons c16315_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(16246, 360), (16247, 360), (16248, 360), (16249, 360), (16250, 720), (16251, 720), (16254, 360), (16255, 360), (16304, 360), (16305, 360), (16306, 720), (16307, 720), (16310, 360), (16311, 360), (16312, 360), (16313, 360), (16314, 720), (16315, 720)]

theorem segOK : checkSeg 20 perms 16246 16318 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 16246 16318 8640 272285225280 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 272285225280)
    (SegSum.cons (w := 360) h16246 (SegSum.cons (w := 360) h16247 (SegSum.cons (w := 360) h16248 (SegSum.cons (w := 360) h16249 (SegSum.cons (w := 720) h16250 (SegSum.cons (w := 720) h16251 (SegSum.cons (w := 360) h16254 (SegSum.cons (w := 360) h16255 (SegSum.cons (w := 360) h16304 (SegSum.cons (w := 360) h16305 (SegSum.cons (w := 720) h16306 (SegSum.cons (w := 720) h16307 (SegSum.cons (w := 360) h16310 (SegSum.cons (w := 360) h16311 (SegSum.cons (w := 360) h16312 (SegSum.cons (w := 360) h16313 (SegSum.cons (w := 720) h16314 (SegSum.cons (w := 720) h16315 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S33
