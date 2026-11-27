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

namespace RACert.S4N1.C0.S34

open RACert RACert.Problem

theorem cover5968 : P.CoversSplit 24 10 5968 0xf888f888a080a080f888f888a080a080a080a08000000000a080a08000000000c800c80080008000c800c8008000800080008000000000008000800000000000c800c80080008000c800c80080008000f888f88800000000f888f888000000000000000000000000000000000000000000000000800080000000000080008000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 516, 572, 860, 916, 1202, 1217, 1258, 1259, 1601, 1609]) (ps := [(2, [465, 468], [466, 472]), (5, [516, 523, 565], [516, 523]), (8, [537, 586], [516, 572]), (14, [874, 923], [860, 916])]) (by decide +kernel)

theorem c5968_0 : P.sumLeaves 24 6111232 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5968) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover5968 (by decide)
  decide +kernel

theorem contract5968_1 : P.leaf 30 95492 = 0 := by
  exact leaf_contract_zero (ss := [(7, 6, 467), (2, 1, 468), (6, 1, 479), (15, 1, 486), (14, 8, 509), (8, 1, 482), (5, 1, 523), (3, 1, 409), (4, 1, 410), (10, 1, 458), (11, 1, 459), (12, 1, 460), (17, 1, 537), (31, 1, 565), (26, 1, 516), (27, 1, 572), (19, 1, 586), (28, 1, 860), (16, 1, 874), (29, 1, 916), (18, 1, 923)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c5968_1 : P.sumLeaves 24 6111488 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 95492) rows (by decide) (by decide)).symm.trans contract5968_1

theorem contract5968_2 : P.leaf 30 95493 = 0 := by
  exact leaf_contract_zero (ss := [(7, 6, 467), (2, 1, 468), (6, 1, 479), (15, 1, 486), (14, 8, 509), (8, 1, 482), (5, 1, 523), (3, 1, 409), (4, 1, 410), (10, 1, 458), (11, 1, 459), (12, 1, 460), (17, 1, 537), (31, 1, 565), (26, 1, 516), (27, 1, 572), (19, 1, 586), (28, 1, 860), (16, 1, 874), (29, 1, 916), (18, 1, 923)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c5968_2 : P.sumLeaves 24 6111552 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 95493) rows (by decide) (by decide)).symm.trans contract5968_2

theorem contract5968_3 : P.leaf 30 95494 = 2880 := by
  exact leaf_contract_factors (k := 30) (b := 14) (H := 95494) (ss := [(7, 6, 467), (2, 1, 468), (6, 1, 479), (15, 1, 486), (14, 8, 509), (8, 1, 482), (5, 1, 523), (3, 1, 409), (4, 1, 410), (10, 1, 458), (11, 1, 459), (12, 1, 460), (27, 1, 572), (19, 1, 586), (29, 1, 916), (18, 1, 923)]) (ids := [7, 11, 14, 15, 18, 19, 22, 24, 26, 28, 29, 20, 21, 23]) (cs := [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 5, 1, 1, 6, 7, 13, 14, 8, 15, 9, 1, 10, 1, 11, 12]) (bs := [11, 3]) (W := 2880) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c5968_3 : P.sumLeaves 24 6111616 64 = 2880 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 95494) rows (by decide) (by decide)).symm.trans contract5968_3

theorem contract5968_4 : P.leaf 30 95495 = 2880 := by
  exact leaf_contract_factors (k := 30) (b := 14) (H := 95495) (ss := [(7, 6, 467), (2, 1, 468), (6, 1, 479), (15, 1, 486), (14, 8, 509), (8, 1, 482), (5, 1, 523), (3, 1, 409), (4, 1, 410), (10, 1, 458), (11, 1, 459), (12, 1, 460), (27, 1, 572), (19, 1, 586), (29, 1, 916), (18, 1, 923)]) (ids := [7, 11, 14, 15, 18, 19, 22, 24, 26, 28, 29, 20, 21, 23]) (cs := [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 5, 1, 1, 6, 7, 13, 14, 8, 15, 9, 1, 10, 1, 11, 12]) (bs := [11, 3]) (W := 2880) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c5968_4 : P.sumLeaves 24 6111680 64 = 2880 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 95495) rows (by decide) (by decide)).symm.trans contract5968_4

theorem c5968_5 : P.sumLeaves 24 6111744 128 = 640 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5968) (lo := 512) (len := 128) (W := 640) check rows elimOK (by decide) (by decide) cover5968 (by decide)
  decide +kernel

theorem contract5968_6 : P.leaf 30 95498 = 2880 := by
  exact leaf_contract_factors (k := 30) (b := 14) (H := 95498) (ss := [(7, 6, 467), (2, 1, 468), (6, 1, 479), (15, 1, 486), (14, 8, 509), (8, 1, 482), (5, 1, 523), (3, 1, 409), (4, 1, 410), (10, 1, 458), (11, 1, 459), (12, 1, 460), (19, 1, 529), (27, 1, 572), (18, 1, 879), (29, 1, 916)]) (ids := [7, 11, 14, 15, 18, 19, 22, 24, 26, 28, 29, 20, 21, 23]) (cs := [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 5, 1, 1, 6, 7, 13, 14, 8, 15, 9, 1, 10, 1, 11, 12]) (bs := [11, 3]) (W := 2880) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c5968_6 : P.sumLeaves 24 6111872 64 = 2880 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 95498) rows (by decide) (by decide)).symm.trans contract5968_6

theorem contract5968_7 : P.leaf 30 95499 = 2880 := by
  exact leaf_contract_factors (k := 30) (b := 14) (H := 95499) (ss := [(7, 6, 467), (2, 1, 468), (6, 1, 479), (15, 1, 486), (14, 8, 509), (8, 1, 482), (5, 1, 523), (3, 1, 409), (4, 1, 410), (10, 1, 458), (11, 1, 459), (12, 1, 460), (19, 1, 529), (27, 1, 572), (18, 1, 879), (29, 1, 916)]) (ids := [7, 11, 14, 15, 18, 19, 22, 24, 26, 28, 29, 20, 21, 23]) (cs := [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 5, 1, 1, 6, 7, 13, 14, 8, 15, 9, 1, 10, 1, 11, 12]) (bs := [11, 3]) (W := 2880) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c5968_7 : P.sumLeaves 24 6111936 64 = 2880 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 95499) rows (by decide) (by decide)).symm.trans contract5968_7

theorem contract5968_8 : P.leaf 30 95500 = 2560 := by
  exact leaf_contract_factors (k := 30) (b := 13) (H := 95500) (ss := [(7, 6, 467), (2, 1, 468), (6, 1, 479), (15, 1, 486), (14, 8, 509), (8, 1, 482), (5, 1, 523), (3, 1, 409), (4, 1, 410), (10, 1, 458), (11, 1, 459), (12, 1, 460), (17, 1, 537), (31, 1, 565), (26, 1, 516), (28, 1, 860), (16, 1, 874)]) (ids := [7, 11, 16, 17, 18, 19, 23, 25, 27, 20, 21, 22, 28]) (cs := [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 5, 6, 7, 11, 12, 13, 8, 1, 9, 1, 10, 14, 1]) (bs := [9, 4]) (W := 2560) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c5968_8 : P.sumLeaves 24 6112000 64 = 2560 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 95500) rows (by decide) (by decide)).symm.trans contract5968_8

theorem contract5968_9 : P.leaf 30 95501 = 2560 := by
  exact leaf_contract_factors (k := 30) (b := 13) (H := 95501) (ss := [(7, 6, 467), (2, 1, 468), (6, 1, 479), (15, 1, 486), (14, 8, 509), (8, 1, 482), (5, 1, 523), (3, 1, 409), (4, 1, 410), (10, 1, 458), (11, 1, 459), (12, 1, 460), (17, 1, 537), (31, 1, 565), (26, 1, 516), (28, 1, 860), (16, 1, 874)]) (ids := [7, 11, 16, 17, 18, 19, 23, 25, 27, 20, 21, 22, 28]) (cs := [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 5, 6, 7, 11, 12, 13, 8, 1, 9, 1, 10, 14, 1]) (bs := [9, 4]) (W := 2560) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c5968_9 : P.sumLeaves 24 6112064 64 = 2560 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 95501) rows (by decide) (by decide)).symm.trans contract5968_9

theorem contract5968_10 : P.leaf 30 95502 = 15680 := by
  exact leaf_contract_factors (k := 30) (b := 18) (H := 95502) (ss := [(7, 6, 467), (2, 1, 468), (6, 1, 479), (15, 1, 486), (14, 8, 509), (8, 1, 482), (5, 1, 523), (3, 1, 409), (4, 1, 410), (10, 1, 458), (11, 1, 459), (12, 1, 460)]) (ids := [7, 11, 14, 15, 16, 17, 18, 19, 22, 23, 24, 25, 26, 27, 28, 29, 20, 21]) (cs := [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 5, 6, 7, 8, 9, 18, 19, 10, 11, 12, 13, 14, 15, 16, 17]) (bs := [16, 2]) (W := 15680) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c5968_10 : P.sumLeaves 24 6112128 64 = 15680 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 95502) rows (by decide) (by decide)).symm.trans contract5968_10

theorem contract5968_11 : P.leaf 30 95503 = 15680 := by
  exact leaf_contract_factors (k := 30) (b := 18) (H := 95503) (ss := [(7, 6, 467), (2, 1, 468), (6, 1, 479), (15, 1, 486), (14, 8, 509), (8, 1, 482), (5, 1, 523), (3, 1, 409), (4, 1, 410), (10, 1, 458), (11, 1, 459), (12, 1, 460)]) (ids := [7, 11, 14, 15, 16, 17, 18, 19, 22, 24, 25, 26, 27, 28, 29, 20, 21, 23]) (cs := [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 5, 6, 7, 8, 9, 17, 18, 10, 19, 11, 12, 13, 14, 15, 16]) (bs := [15, 3]) (W := 15680) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c5968_11 : P.sumLeaves 24 6112192 64 = 15680 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 95503) rows (by decide) (by decide)).symm.trans contract5968_11

theorem h5968 : P.leaf 34 5968 = 48640 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 0), (64, 0), (64, 2880), (64, 2880), (128, 640), (64, 2880), (64, 2880), (64, 2560), (64, 2560), (64, 15680), (64, 15680)]) (.cons c5968_0 (.cons c5968_1 (.cons c5968_2 (.cons c5968_3 (.cons c5968_4 (.cons c5968_5 (.cons c5968_6 (.cons c5968_7 (.cons c5968_8 (.cons c5968_9 (.cons c5968_10 (.cons c5968_11 (.nil))))))))))))) (by decide) (by decide))

theorem cover5969 : P.CoversSplit 24 10 5969 0xffffffffa0a0a0a0ffccffcca080a080ffffffff00000000ffccffcc00000000cc00cc0080008000cc00cc0080008000cc00cc0000000000cc00cc0000000000cc00cc0080008000cc00cc0080008000ffffffff00000000ffccffcc000000000000000000000000000000000000000000330033000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 516, 572, 860, 916, 1217, 1258, 1259, 1601, 1609]) (ps := [(5, [453], [565, 572]), (8, [586], [572]), (14, [923], [916])]) (by decide +kernel)

theorem c5969_0 : P.sumLeaves 24 6112256 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5969) (lo := 0) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover5969 (by decide)
  decide +kernel

theorem contract5969_1 : P.leaf 30 95505 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 453), (5, 1, 453), (7, 6, 474), (6, 1, 478), (12, 1, 460), (15, 1, 487), (14, 8, 558), (8, 1, 482), (17, 1, 537), (3, 1, 536), (31, 1, 565), (27, 0, 572), (19, 4, 578), (4, 1, 587), (9, 1, 587), (10, 1, 872), (16, 1, 874), (29, 0, 916), (18, 11, 921), (11, 1, 922), (13, 1, 922)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c5969_1 : P.sumLeaves 24 6112320 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 95505) rows (by decide) (by decide)).symm.trans contract5969_1

theorem c5969_2 : P.sumLeaves 24 6112384 128 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5969) (lo := 128) (len := 128) (W := 0) check rows elimOK (by decide) (by decide) cover5969 (by decide)
  decide +kernel

theorem contract5969_3 : P.leaf 30 95508 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 453), (5, 1, 453), (7, 6, 474), (6, 1, 478), (12, 1, 460), (15, 1, 487), (14, 8, 558), (8, 1, 482), (17, 1, 537), (31, 1, 565), (27, 1, 572), (16, 1, 874), (29, 1, 916)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c5969_3 : P.sumLeaves 24 6112512 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 95508) rows (by decide) (by decide)).symm.trans contract5969_3

theorem contract5969_4 : P.leaf 30 95509 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 453), (5, 1, 453), (7, 6, 474), (6, 1, 478), (12, 1, 460), (15, 1, 487), (14, 8, 558), (8, 1, 482), (17, 1, 537), (31, 1, 565), (27, 1, 572), (16, 1, 874), (29, 1, 916)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c5969_4 : P.sumLeaves 24 6112576 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 95509) rows (by decide) (by decide)).symm.trans contract5969_4

theorem contract5969_5 : P.leaf 30 95510 = 38800 := by
  exact leaf_contract_factors (k := 30) (b := 18) (H := 95510) (ss := [(2, 1, 453), (5, 1, 453), (7, 6, 474), (6, 1, 478), (12, 1, 460), (15, 1, 487), (14, 8, 558), (8, 1, 488), (27, 1, 572), (19, 1, 586), (29, 1, 916), (18, 1, 923)]) (ids := [1, 2, 7, 8, 9, 11, 14, 15, 18, 19, 22, 24, 26, 28, 29, 20, 21, 23]) (cs := [1, 2, 3, 1, 1, 1, 1, 4, 5, 6, 1, 7, 1, 1, 8, 9, 1, 1, 10, 11, 17, 18, 12, 19, 13, 1, 14, 1, 15, 16]) (bs := [15, 3]) (W := 38800) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c5969_5 : P.sumLeaves 24 6112640 64 = 38800 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 95510) rows (by decide) (by decide)).symm.trans contract5969_5

theorem contract5969_6 : P.leaf 30 95511 = 61120 := by
  exact leaf_contract_factors (k := 30) (b := 18) (H := 95511) (ss := [(2, 1, 453), (5, 1, 453), (7, 6, 474), (6, 1, 478), (12, 1, 460), (15, 1, 487), (14, 8, 558), (8, 1, 488), (27, 1, 572), (19, 1, 586), (29, 1, 916), (18, 1, 923)]) (ids := [1, 2, 7, 8, 9, 11, 14, 15, 18, 19, 22, 24, 26, 28, 29, 20, 21, 23]) (cs := [1, 2, 3, 1, 1, 1, 1, 4, 5, 6, 1, 7, 1, 1, 8, 9, 1, 1, 10, 11, 17, 18, 12, 19, 13, 1, 14, 1, 15, 16]) (bs := [15, 3]) (W := 61120) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c5969_6 : P.sumLeaves 24 6112704 64 = 61120 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 95511) rows (by decide) (by decide)).symm.trans contract5969_6

theorem contract5969_7 : P.leaf 30 95512 = 6792 := by
  exact leaf_contract_factors (k := 30) (b := 15) (H := 95512) (ss := [(2, 1, 453), (5, 1, 453), (7, 6, 474), (6, 1, 478), (12, 1, 460), (15, 1, 487), (8, 1, 537), (17, 1, 537), (14, 1, 558), (31, 1, 565), (27, 1, 572), (19, 1, 578), (16, 1, 874), (29, 1, 916), (18, 1, 921)]) (ids := [1, 2, 7, 8, 9, 11, 18, 19, 22, 24, 26, 28, 20, 21, 23]) (cs := [1, 2, 3, 1, 1, 1, 1, 4, 5, 6, 1, 7, 1, 1, 1, 1, 1, 1, 8, 9, 14, 15, 10, 16, 11, 1, 12, 1, 13, 1]) (bs := [12, 3]) (W := 6792) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c5969_7 : P.sumLeaves 24 6112768 64 = 6792 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 95512) rows (by decide) (by decide)).symm.trans contract5969_7

theorem contract5969_8 : P.leaf 30 95513 = 10848 := by
  exact leaf_contract_factors (k := 30) (b := 15) (H := 95513) (ss := [(2, 1, 453), (5, 1, 453), (7, 6, 474), (6, 1, 478), (12, 1, 460), (15, 1, 487), (8, 1, 537), (17, 1, 537), (14, 1, 558), (31, 1, 565), (27, 1, 572), (19, 1, 578), (16, 1, 874), (29, 1, 916), (18, 1, 921)]) (ids := [1, 7, 8, 11, 18, 19, 22, 24, 26, 28, 2, 9, 20, 21, 23]) (cs := [1, 2, 12, 1, 1, 1, 1, 3, 4, 13, 1, 5, 1, 1, 1, 1, 1, 1, 6, 7, 14, 15, 8, 16, 9, 1, 10, 1, 11, 1]) (bs := [10, 5]) (W := 10848) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c5969_8 : P.sumLeaves 24 6112832 64 = 10848 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 95513) rows (by decide) (by decide)).symm.trans contract5969_8

theorem contract5969_9 : P.leaf 30 95514 = 38800 := by
  exact leaf_contract_factors (k := 30) (b := 18) (H := 95514) (ss := [(2, 1, 453), (5, 1, 453), (7, 6, 474), (6, 1, 478), (12, 1, 460), (15, 1, 487), (14, 8, 558), (8, 1, 488), (27, 1, 572), (19, 1, 578), (29, 1, 916), (18, 1, 921)]) (ids := [1, 2, 7, 8, 9, 11, 14, 15, 18, 19, 22, 24, 26, 28, 29, 20, 21, 23]) (cs := [1, 2, 3, 1, 1, 1, 1, 4, 5, 6, 1, 7, 1, 1, 8, 9, 1, 1, 10, 11, 17, 18, 12, 19, 13, 1, 14, 1, 15, 16]) (bs := [15, 3]) (W := 38800) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c5969_9 : P.sumLeaves 24 6112896 64 = 38800 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 95514) rows (by decide) (by decide)).symm.trans contract5969_9

theorem contract5969_10 : P.leaf 30 95515 = 61120 := by
  exact leaf_contract_factors (k := 30) (b := 18) (H := 95515) (ss := [(2, 1, 453), (5, 1, 453), (7, 6, 474), (6, 1, 478), (12, 1, 460), (15, 1, 487), (14, 8, 558), (8, 1, 488), (27, 1, 572), (19, 1, 578), (29, 1, 916), (18, 1, 921)]) (ids := [1, 2, 7, 8, 9, 11, 14, 15, 18, 19, 22, 24, 26, 28, 29, 20, 21, 23]) (cs := [1, 2, 3, 1, 1, 1, 1, 4, 5, 6, 1, 7, 1, 1, 8, 9, 1, 1, 10, 11, 17, 18, 12, 19, 13, 1, 14, 1, 15, 16]) (bs := [15, 3]) (W := 61120) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c5969_10 : P.sumLeaves 24 6112960 64 = 61120 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 95515) rows (by decide) (by decide)).symm.trans contract5969_10

theorem contract5969_11 : P.leaf 30 95516 = 44992 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 95516) (ss := [(2, 1, 453), (5, 1, 453), (7, 6, 474), (6, 1, 478), (12, 1, 460), (15, 1, 487), (8, 1, 537), (17, 1, 537), (14, 1, 558), (31, 1, 565), (16, 1, 874)]) (ids := [1, 2, 7, 8, 9, 11, 16, 17, 18, 19, 22, 23, 24, 25, 26, 27, 28, 20, 21]) (cs := [1, 2, 3, 1, 1, 1, 1, 4, 5, 6, 1, 7, 1, 1, 1, 1, 8, 9, 10, 11, 19, 20, 12, 13, 14, 15, 16, 17, 18, 1]) (bs := [17, 2]) (W := 44992) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c5969_11 : P.sumLeaves 24 6113024 64 = 44992 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 95516) rows (by decide) (by decide)).symm.trans contract5969_11

theorem contract5969_12 : P.leaf 30 95517 = 70228 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 95517) (ss := [(2, 1, 453), (5, 1, 453), (7, 6, 474), (6, 1, 478), (12, 1, 460), (15, 1, 487), (8, 1, 537), (17, 1, 537), (14, 1, 558), (31, 1, 565), (16, 1, 874)]) (ids := [1, 2, 7, 8, 9, 11, 16, 17, 18, 19, 22, 23, 24, 25, 26, 27, 28, 20, 21]) (cs := [1, 2, 3, 1, 1, 1, 1, 4, 5, 6, 1, 7, 1, 1, 1, 1, 8, 9, 10, 11, 19, 20, 12, 13, 14, 15, 16, 17, 18, 1]) (bs := [17, 2]) (W := 70228) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c5969_12 : P.sumLeaves 24 6113088 64 = 70228 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 95517) rows (by decide) (by decide)).symm.trans contract5969_12

theorem c5969_13 : P.sumLeaves 24 6113152 128 = 478608 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5969) (lo := 896) (len := 128) (W := 478608) check rows elimOK (by decide) (by decide) cover5969 (by decide)
  decide +kernel

theorem h5969 : P.leaf 34 5969 = 811308 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 0), (64, 0), (128, 0), (64, 0), (64, 0), (64, 38800), (64, 61120), (64, 6792), (64, 10848), (64, 38800), (64, 61120), (64, 44992), (64, 70228), (128, 478608)]) (.cons c5969_0 (.cons c5969_1 (.cons c5969_2 (.cons c5969_3 (.cons c5969_4 (.cons c5969_5 (.cons c5969_6 (.cons c5969_7 (.cons c5969_8 (.cons c5969_9 (.cons c5969_10 (.cons c5969_11 (.cons c5969_12 (.cons c5969_13 (.nil))))))))))))))) (by decide) (by decide))

theorem cover5971 : P.CoversSplit 24 10 5971 0xffffffffa0a0a0a0ffffffffa0a0a0a0ffffffff00000000ffffffff00000000cc00cc0080008000cc00cc0080008000cc00cc0000000000cc00cc0000000000ffffffffa0a0a0a0ffffffffa0a0a0a0ffffffffa0a0a0a0ffffffffa0a0a0a000000000000000000000000000000000cc00cc0080008000cc00cc0080008000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 572, 860, 916, 1217, 1609]) (ps := [(8, [537, 586], [1217, 1609])]) (by decide +kernel)

noncomputable def f5971 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (6114304 + i)

theorem c5971_0 : rowSum f5971 0 455 = 338200 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5971) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover5971 (by decide)
  decide +kernel

theorem c5971_1 : rowSum f5971 455 569 = 1806592 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5971) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover5971 (by decide)
  decide +kernel

theorem sum5971 : rowSum f5971 0 1024 = 2144792 :=
  rowSum_append (F := f5971) (lo := 0) (n := 455) (m := 569) (A := 338200) (B := 1806592) c5971_0 (c5971_1)

theorem h5971 : P.leaf 34 5971 = 2144792 :=
  leaf_weighted (k := 24) (d := 10) (H := 5971) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 5971) (by decide) (by decide +kernel)) sum5971

theorem cover5972 : P.CoversSplit 24 10 5972 0xffffffffa0a0a0a0ffffffffa0a0a0a0a4a0a4a000000000a4a0a4a000000000cc00cc0080008000cc00cc008000800084008400000000008400840000000000cc20cc2080208020cc20cc2080208020842084200000000084208420000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 516, 523, 565, 572, 860, 916, 1202, 1258, 1259, 1601]) (ps := [(2, [468, 475], [466, 472])]) (by decide +kernel)

noncomputable def f5972 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (6115328 + i)

theorem c5972_0 : rowSum f5972 0 1024 = 520316 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5972) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover5972 (by decide)
  decide +kernel

theorem sum5972 : rowSum f5972 0 1024 = 520316 :=
  c5972_0

theorem h5972 : P.leaf 34 5972 = 520316 :=
  leaf_weighted (k := 24) (d := 10) (H := 5972) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 5972) (by decide) (by decide +kernel)) sum5972

theorem cover5973 : P.CoversSplit 24 10 5973 0xffffffffa0a0a0a0ffffffffa0a0a0a0ffffffff00000000ffffffff00000000cc00cc0080008000cc00cc0080008000cc00cc0000000000cc00cc0000000000cc33cc3380208020cc33cc3380208020cc33cc3300000000cc33cc33000000000000000000000000000000000000000000330033000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 516, 565, 572, 916, 1202, 1258, 1259, 1601, 1609]) (by decide +kernel)

noncomputable def f5973 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 24 (6116352 + i)

theorem c5973_0 : rowSum f5973 0 807 = 1413264 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5973) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover5973 (by decide)
  decide +kernel

theorem c5973_1 : rowSum f5973 807 217 = 7183937 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5973) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover5973 (by decide)
  decide +kernel

theorem sum5973 : rowSum f5973 0 1024 = 8597201 :=
  rowSum_append (F := f5973) (lo := 0) (n := 807) (m := 217) (A := 1413264) (B := 7183937) c5973_0 (c5973_1)

theorem h5973 : P.leaf 34 5973 = 8597201 :=
  leaf_weighted (k := 24) (d := 10) (H := 5973) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 5973) (by decide) (by decide +kernel)) sum5973

theorem cover5975 : P.CoversSplit 24 10 5975 0xffffffffa0a0a0a0ffffffffa0a0a0a0ffffffff0000a0a0ffffffff0000a0a0cc00cc0080008000cc00cc0080008000cc00cc0000008000cc00cc0000008000ffffffffa0a0a0a0ffffffffa0a0a0a0ffffffffa0a0a0a0ffffffffa0a0a0a00000000000000000cc00cc0080008000cc00cc0080008000cc00cc0080008000 :=
  coversSplit check rows (by decide) (by decide) (xs := [516, 572, 1202, 1217, 1258, 1259, 1601, 1609]) (by decide +kernel)

noncomputable def f5975 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (6118400 + i)

theorem c5975_0 : rowSum f5975 0 439 = 2132660 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5975) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover5975 (by decide)
  decide +kernel

theorem c5975_1 : rowSum f5975 439 572 = 28903268 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5975) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover5975 (by decide)
  decide +kernel

theorem c5975_2 : rowSum f5975 1011 13 = 6357156 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5975) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover5975 (by decide)
  decide +kernel

theorem sum5975 : rowSum f5975 0 1024 = 37393084 :=
  rowSum_append (F := f5975) (lo := 0) (n := 439) (m := 585) (A := 2132660) (B := 35260424) c5975_0 (rowSum_append (F := f5975) (lo := 439) (n := 572) (m := 13) (A := 28903268) (B := 6357156) c5975_1 (c5975_2))

theorem h5975 : P.leaf 34 5975 = 37393084 :=
  leaf_weighted (k := 24) (d := 10) (H := 5975) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 5975) (by decide) (by decide +kernel)) sum5975

theorem cover5976 : P.CoversSplit 24 10 5976 0xffffffffa0a0a0a0ffffffffa0a0a0a0a0a0a0a000000000a0a0a0a000000000cc00cc0080008000cc00cc008000800080008000000000008000800000000000cc00cc0080008000cc00cc0080008000ffffffff00000000ffffffff000000000000000000000000000000000000000000000000800080000000000080008000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 516, 572, 860, 916, 1202, 1217, 1258, 1259, 1601, 1609]) (ps := [(5, [516, 523, 565], [516, 523]), (7, [467, 474], [516, 572]), (14, [874, 923], [860, 916])]) (by decide +kernel)

noncomputable def f5976 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (6119424 + i)

theorem c5976_0 : rowSum f5976 0 952 = 436442 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5976) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover5976 (by decide)
  decide +kernel

theorem c5976_1 : rowSum f5976 952 72 = 384004 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5976) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover5976 (by decide)
  decide +kernel

theorem sum5976 : rowSum f5976 0 1024 = 820446 :=
  rowSum_append (F := f5976) (lo := 0) (n := 952) (m := 72) (A := 436442) (B := 384004) c5976_0 (c5976_1)

theorem h5976 : P.leaf 34 5976 = 820446 :=
  leaf_weighted (k := 24) (d := 10) (H := 5976) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 5976) (by decide) (by decide +kernel)) sum5976

theorem cover5977 : P.CoversSplit 24 10 5977 0xffffffffa0a0a0a0ffffffffa0a0a0a0ffffffff00000000ffffffff00000000cc00cc0080008000cc00cc0080008000cc00cc0000000000cc00cc0000000000cc00cc0080008000cc00cc0080008000ffffffff00000000ffffffff000000000000000000000000000000000000000000330033000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 516, 572, 860, 916, 1217, 1258, 1259, 1601, 1609]) (ps := [(5, [516, 523], [565, 572]), (8, [586], [572]), (14, [923], [916])]) (by decide +kernel)

noncomputable def f5977 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 24 (6120448 + i)

theorem c5977_0 : rowSum f5977 0 807 = 492492 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5977) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover5977 (by decide)
  decide +kernel

theorem c5977_1 : rowSum f5977 807 217 = 1583586 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5977) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover5977 (by decide)
  decide +kernel

theorem sum5977 : rowSum f5977 0 1024 = 2076078 :=
  rowSum_append (F := f5977) (lo := 0) (n := 807) (m := 217) (A := 492492) (B := 1583586) c5977_0 (c5977_1)

theorem h5977 : P.leaf 34 5977 = 2076078 :=
  leaf_weighted (k := 24) (d := 10) (H := 5977) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 5977) (by decide) (by decide +kernel)) sum5977

theorem cover5979 : P.CoversSplit 24 10 5979 0xffffffffa0a0a0a0ffffffffa0a0a0a0ffffffff00000000ffffffff00000000cc00cc0080008000cc00cc0080008000cc00cc0000000000cc00cc0000000000ffffffffa0a0a0a0ffffffffa0a0a0a0ffffffffa0a0a0a0ffffffffa0a0a0a000000000000000000000000000000000cc00cc0080008000cc00cc0080008000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 572, 860, 916, 1217, 1609]) (ps := [(8, [537, 586], [1217, 1609])]) (by decide +kernel)

noncomputable def f5979 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (6122496 + i)

theorem c5979_0 : rowSum f5979 0 455 = 944116 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5979) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover5979 (by decide)
  decide +kernel

theorem c5979_1 : rowSum f5979 455 569 = 6220241 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5979) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover5979 (by decide)
  decide +kernel

theorem sum5979 : rowSum f5979 0 1024 = 7164357 :=
  rowSum_append (F := f5979) (lo := 0) (n := 455) (m := 569) (A := 944116) (B := 6220241) c5979_0 (c5979_1)

theorem h5979 : P.leaf 34 5979 = 7164357 :=
  leaf_weighted (k := 24) (d := 10) (H := 5979) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 5979) (by decide) (by decide +kernel)) sum5979

theorem cover5980 : P.CoversSplit 24 10 5980 0xffffffffa0a0a0a0ffffffffa0a0a0a0a5a5a5a500000000a5a5a5a500000000cc00cc0080008000cc00cc008000800084008400000000008400840000000000cc33cc3380208020cc33cc3380208020842184210000000084218421000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 516, 523, 565, 572, 860, 916, 1202, 1258, 1259, 1601]) (by decide +kernel)

noncomputable def f5980 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (6123520 + i)

theorem c5980_0 : rowSum f5980 0 1009 = 3022946 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5980) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover5980 (by decide)
  decide +kernel

theorem c5980_1 : rowSum f5980 1009 15 = 770984 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5980) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover5980 (by decide)
  decide +kernel

theorem sum5980 : rowSum f5980 0 1024 = 3793930 :=
  rowSum_append (F := f5980) (lo := 0) (n := 1009) (m := 15) (A := 3022946) (B := 770984) c5980_0 (c5980_1)

theorem h5980 : P.leaf 34 5980 = 3793930 :=
  leaf_weighted (k := 24) (d := 10) (H := 5980) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 5980) (by decide) (by decide +kernel)) sum5980

theorem cover5981 : P.CoversSplit 24 10 5981 0xffffffffa0a0a0a0ffffffffa0a0a0a0ffffffff00000000ffffffff00000000cc00cc0080008000cc00cc0080008000cc00cc0000000000cc00cc0000000000cc33cc3380208020cc33cc3380208020cc33cc3300000000cc33cc33000000000000000000000000000000000000000000330033000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 516, 565, 572, 916, 1202, 1258, 1259, 1601, 1609]) (by decide +kernel)

noncomputable def f5981 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 24 (6124544 + i)

theorem c5981_0 : rowSum f5981 0 807 = 2738284 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5981) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover5981 (by decide)
  decide +kernel

theorem c5981_1 : rowSum f5981 807 217 = 11122259 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5981) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover5981 (by decide)
  decide +kernel

theorem sum5981 : rowSum f5981 0 1024 = 13860543 :=
  rowSum_append (F := f5981) (lo := 0) (n := 807) (m := 217) (A := 2738284) (B := 11122259) c5981_0 (c5981_1)

theorem h5981 : P.leaf 34 5981 = 13860543 :=
  leaf_weighted (k := 24) (d := 10) (H := 5981) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 5981) (by decide) (by decide +kernel)) sum5981

def seg : List (ℕ × ℕ) := [(5968, 12), (5969, 24), (5971, 12), (5972, 12), (5973, 24), (5975, 12), (5976, 12), (5977, 24), (5979, 12), (5980, 12), (5981, 24)]

theorem segOK : checkSeg 16 perms 5968 5983 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 5968 5983 180 1230909900 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1230909900)
    (SegSum.cons (w := 12) h5968 (SegSum.cons (w := 24) h5969 (SegSum.cons (w := 12) h5971 (SegSum.cons (w := 12) h5972 (SegSum.cons (w := 24) h5973 (SegSum.cons (w := 12) h5975 (SegSum.cons (w := 12) h5976 (SegSum.cons (w := 24) h5977 (SegSum.cons (w := 12) h5979 (SegSum.cons (w := 12) h5980 (SegSum.cons (w := 24) h5981 (show SegSum (P.leaf 34) [] 0 from rfl)))))))))))) (by decide)

end RACert.S4N1.C0.S34
