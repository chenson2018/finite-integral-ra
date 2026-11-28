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

namespace RACert.S4N1.C0.S2

open RACert RACert.Problem

theorem cover484 : P.CoversSplit 24 10 484 0x8000000000004000000000000000000080000000000040000000000000000000000000001000100020000000100000000000000010001000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000010000000200000001000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 468, 473, 475, 515, 522, 858, 860, 865, 916, 1217, 1266, 1609]) (by decide +kernel)

theorem h484 : P.leaf 34 484 = 39256 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 484) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 484) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 484) (weight := rowWeight keep0 twice0) (xs := [156, 189, 220, 511, 588, 604, 668, 701, 716, 732, 846, 895, 974, 1023]) check rows elimOK (by decide) (by decide) cover484 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h236 : P.leaf 34 236 = 39256 :=
  orient24 (v := 484) (by decide) (by decide +kernel) h484

theorem cover237 : P.CoversSplit 24 10 237 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem h237 : P.leaf 34 237 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 237) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 237) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover237 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover238 : P.CoversSplit 24 10 238 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem h238 : P.leaf 34 238 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 238) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 238) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover238 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover239 : P.CoversSplit 24 10 239 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem h239 : P.leaf 34 239 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 239) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 239) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover239 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover254 : P.CoversSplit 24 10 254 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem h254 : P.leaf 34 254 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 254) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 254) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover254 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover255 : P.CoversSplit 24 10 255 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h255 : P.leaf 34 255 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 255) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 255) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover255 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover492 : P.CoversSplit 24 10 492 0x8000000000004400000000000000000080000000000040000000000000000000000000001001110120200000101100000000000010011000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000010010000200000001000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 473, 515, 522, 858, 859, 865, 915, 1217, 1266, 1609]) (by decide +kernel)

theorem h492 : P.leaf 34 492 = 197208 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 492) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 492) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 492) (weight := rowWeight keep0 twice0) (xs := [156, 189, 208, 220, 511, 588, 592, 604, 656, 660, 668, 693, 701, 704, 712, 716, 720, 732, 846, 895, 970, 974, 1023]) check rows elimOK (by decide) (by decide) cover492 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover493 : P.CoversSplit 24 10 493 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem h493 : P.leaf 34 493 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 493) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 493) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover493 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover495 : P.CoversSplit 24 10 495 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem h495 : P.leaf 34 495 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 495) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 495) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover495 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover511 : P.CoversSplit 24 10 511 0xfff8faf8faf8aaa8ffc8fac8fac8aa88fff8faf8faf8aaa8ffc8fac8fac8aa88ffc8fac888888888ccc8c8c888888888ffc8fac888888888ccc8c8c888888888fff8faf8faf8aaa8ffc8fac8fac8aa88fff8faf8faf8aaa8ffc8fac8fac8aa88ffc8fac888888888ccc8c8c888888888ffc8fac888888888ccc8c8c888888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [858, 859, 865, 915, 1209, 1258]) (by decide +kernel)

noncomputable def f511 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (523264 + i)

theorem c511_0 : rowSum f511 0 301 = 15374244 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 511) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover511 (by decide)
  decide +kernel

theorem c511_1 : rowSum f511 301 209 = 41317056 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 511) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover511 (by decide)
  decide +kernel

theorem c511_2 : rowSum f511 510 514 = 53932314 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 511) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover511 (by decide)
  decide +kernel

theorem sum511 : rowSum f511 0 1024 = 110623614 :=
  rowSum_append (F := f511) (lo := 0) (n := 301) (m := 723) (A := 15374244) (B := 95249370) c511_0 (rowSum_append (F := f511) (lo := 301) (n := 209) (m := 514) (A := 41317056) (B := 53932314) c511_1 (c511_2))

theorem h511 : P.leaf 34 511 = 110623614 :=
  leaf_weighted (k := 24) (d := 10) (H := 511) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 511) (by decide) (by decide +kernel)) sum511

theorem cover531 : P.CoversSplit 24 10 531 0xffff00000000000000000000000000008000000000000000000000000000000000000000ffffffff00000000ffffffff0000000000000505000000000000050580000000000000000000000000000000ffffffff00000000ffffffff000000000000000000000000000000000033003300000000ffffffff00000000ffffffff :=
  coversProjected check rows (by decide) (by decide) (xs := [529, 1209, 1217, 1258, 1609]) (ps := [(8, [531, 580], [516, 572, 1217, 1609]), (14, [874, 923], [859, 915, 1217, 1609]), (16, [531], [1258]), (18, [580], [1210])]) (by decide +kernel)

noncomputable def f531 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (543744 + i)

theorem c531_0 : rowSum f531 0 661 = 167819 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 531) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover531 (by decide)
  decide +kernel

theorem c531_1 : rowSum f531 661 363 = 60320 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 531) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover531 (by decide)
  decide +kernel

theorem sum531 : rowSum f531 0 1024 = 228139 :=
  rowSum_append (F := f531) (lo := 0) (n := 661) (m := 363) (A := 167819) (B := 60320) c531_0 (c531_1)

theorem h531 : P.leaf 34 531 = 228139 :=
  leaf_weighted (k := 24) (d := 10) (H := 531) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 531) (by decide) (by decide +kernel)) sum531

theorem cover532 : P.CoversSplit 24 10 532 0x842184210000000084218421000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 468, 473, 475, 508, 516, 523, 529, 572, 860, 916]) (by decide +kernel)

theorem h532 : P.leaf 34 532 = 37 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 532) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 532) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 532) (weight := rowWeight keep0 twice0) (xs := [288, 293, 298, 303, 304, 309, 314, 319, 352, 357, 362, 367, 368, 373, 378, 383]) check rows elimOK (by decide) (by decide) cover532 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover16403 : P.CoversSplit 24 10 16403 0x8008800800000000800880080000000080080000000000008008000000000000000000000000000000000000000000000000000000000000000000000000000080088008000000000000000000000000800880080000000080088008000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 528, 536, 578, 872, 1210, 1259]) (by decide +kernel)

theorem h16403 : P.leaf 34 16403 = 189 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 16403) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 16403) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 16403) (weight := rowWeight keep1 twice1) (xs := [291, 303, 307, 319, 355, 367, 371, 383, 483, 495, 499, 511, 819, 831, 883, 895, 931, 943, 947, 959, 995, 1007, 1011, 1023]) check rows elimOK (by decide) (by decide) cover16403 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h533 : P.leaf 34 533 = 189 :=
  orient32 (v := 16403) (by decide) (by decide +kernel) h16403

theorem cover16915 : P.CoversSplit 24 10 16915 0x8000800000000000800080000000000080000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000080008000000000000000000000000000800080000000000080008000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 528, 536, 578, 871, 921, 1210, 1259]) (by decide +kernel)

theorem h16915 : P.leaf 34 16915 = 2373 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 16915) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 16915) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 16915) (weight := rowWeight keep1 twice1) (xs := [303, 319, 367, 383, 495, 511, 831, 895, 943, 959, 1007, 1023]) check rows elimOK (by decide) (by decide) cover16915 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h535 : P.leaf 34 535 = 2373 :=
  orient32 (v := 16915) (by decide) (by decide +kernel) h16915

theorem cover540 : P.CoversSplit 24 10 540 0x8421000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000842184210000000084218421000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 516, 523, 529, 572, 859, 915, 1209, 1258]) (ps := [(8, [531, 580], [516, 572]), (16, [531], [1258]), (18, [580], [1210])]) (by decide +kernel)

theorem h540 : P.leaf 34 540 = 1912 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 540) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 540) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 540) (weight := rowWeight keep0 twice0) (xs := [288, 293, 298, 303, 304, 309, 314, 319, 352, 357, 362, 367, 368, 373, 378, 383, 511, 895, 1008, 1013, 1018, 1023]) check rows elimOK (by decide) (by decide) cover540 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover541 : P.CoversSplit 24 10 541 0x8421000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000842184210000000084218421000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 516, 523, 529, 572, 859, 915, 1209, 1258]) (ps := [(8, [531, 580], [516, 572]), (16, [531], [1258]), (18, [580], [1210])]) (by decide +kernel)

theorem h541 : P.leaf 34 541 = 26538 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 541) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 541) (weight := fun _ => 1) (xs := [288, 293, 298, 303, 304, 309, 314, 319, 352, 357, 362, 367, 368, 373, 378, 383, 511, 895, 1008, 1013, 1018, 1023]) check rows elimOK (by decide) (by decide) cover541 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover543 : P.CoversSplit 24 10 543 0x8421000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000842184210000000084218421000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 523, 529, 572, 859, 915, 1209, 1258]) (ps := [(8, [531, 580], [516, 572]), (16, [531], [1258]), (18, [580], [1210])]) (by decide +kernel)

theorem h543 : P.leaf 34 543 = 91254 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 543) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 543) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 543) (weight := rowWeight keep0 twice0) (xs := [288, 293, 298, 303, 304, 309, 314, 319, 352, 357, 362, 367, 368, 373, 378, 383, 511, 895, 1008, 1013, 1018, 1023]) check rows elimOK (by decide) (by decide) cover543 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h548 : P.leaf 34 548 = 0 := by
  exact leaf_contract_zero (ss := [(27, 6, 466), (33, 0, 468), (26, 6, 472), (19, 1, 474), (35, 0, 475), (13, 2, 479), (18, 4, 487), (14, 0, 510), (16, 3, 486), (4, 1, 558), (34, 12, 866), (31, 12, 872), (2, 1, 873), (5, 1, 404), (3, 1, 417), (12, 1, 951), (6, 1, 458), (10, 1, 458), (11, 1, 459), (28, 1, 465), (29, 1, 473), (30, 1, 515), (32, 1, 522), (7, 1, 579), (9, 1, 587), (15, 1, 930)]) (q := 958) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover549 : P.CoversSplit 24 10 549 0xc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 475, 515, 517, 522, 572, 859, 860, 871, 872]) (ps := [(14, [958], [1266]), (18, [923], [1210])]) (by decide +kernel)

theorem h549 : P.leaf 34 549 = 192 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 549) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 549) (weight := fun _ => 1) (xs := [510, 511]) check rows elimOK (by decide) (by decide) cover549 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h550 : P.leaf 34 550 = 0 := by
  exact leaf_contract_zero (ss := [(33, 0, 468), (13, 2, 479), (14, 0, 510), (16, 3, 486), (19, 1, 523), (35, 0, 524), (34, 5, 475), (5, 1, 425), (12, 1, 480), (18, 4, 536), (4, 1, 551), (11, 1, 817), (31, 1, 872), (26, 1, 465), (28, 1, 465), (30, 1, 515), (2, 1, 873), (3, 1, 417), (7, 1, 579), (27, 1, 572), (9, 1, 587), (6, 1, 461), (10, 1, 810), (29, 1, 915), (8, 0, 923), (21, 0, 482), (20, 1, 433), (15, 1, 930)]) (q := 958) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover551 : P.CoversSplit 24 10 551 0xc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 517, 522, 524, 572, 859, 860, 871, 872, 916, 1258, 1259]) (ps := [(14, [958], [915, 1266]), (18, [923], [1210])]) (by decide +kernel)

theorem h551 : P.leaf 34 551 = 512 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 551) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 551) (weight := fun _ => 1) (xs := [510, 511]) check rows elimOK (by decide) (by decide) cover551 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover552 : P.CoversSplit 24 10 552 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [558]) (by decide +kernel)

theorem h552 : P.leaf 34 552 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 552) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 552) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover552 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover553 : P.CoversSplit 24 10 553 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [558]) (by decide +kernel)

theorem h553 : P.leaf 34 553 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 553) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 553) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover553 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover554 : P.CoversSplit 24 10 554 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [566]) (by decide +kernel)

theorem h554 : P.leaf 34 554 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 554) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 554) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover554 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover555 : P.CoversSplit 24 10 555 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [566]) (by decide +kernel)

theorem h555 : P.leaf 34 555 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 555) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 555) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover555 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover556 : P.CoversSplit 24 10 556 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [566]) (by decide +kernel)

theorem h556 : P.leaf 34 556 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 556) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 556) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover556 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover557 : P.CoversSplit 24 10 557 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [566]) (by decide +kernel)

theorem h557 : P.leaf 34 557 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 557) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 557) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover557 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover558 : P.CoversSplit 24 10 558 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [566]) (by decide +kernel)

theorem h558 : P.leaf 34 558 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 558) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 558) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover558 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover559 : P.CoversSplit 24 10 559 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [566]) (by decide +kernel)

theorem h559 : P.leaf 34 559 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 559) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 559) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover559 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h566 : P.leaf 34 566 = 0 := by
  exact leaf_contract_zero (ss := [(33, 0, 468), (13, 2, 479), (14, 0, 510), (16, 3, 486), (4, 1, 551), (5, 1, 551), (12, 1, 559), (31, 1, 566), (34, 1, 866), (35, 0, 874), (11, 1, 901), (8, 0, 923), (21, 0, 482), (20, 1, 433)]) (q := 958) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover567 : P.CoversSplit 24 10 567 0xc0000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 529, 572, 859, 860, 867, 871, 916, 1209, 1251, 1258, 1259]) (ps := [(8, [531], [517, 572]), (14, [958], [915, 1266])]) (by decide +kernel)

theorem h567 : P.leaf 34 567 = 10304 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 567) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 567) (weight := fun _ => 1) (xs := [510, 511, 895, 1022, 1023]) check rows elimOK (by decide) (by decide) cover567 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover707 : P.CoversSplit 24 10 707 0xf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [467, 475, 516, 523, 536, 566, 573, 871, 921, 1209, 1258]) (ps := [(14, [1272], [1266])]) (by decide +kernel)

theorem h707 : P.leaf 34 707 = 13296 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 707) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 707) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 707) (weight := rowWeight keep1 twice1) (xs := [1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover707 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h570 : P.leaf 34 570 = 13296 :=
  orient24 (v := 707) (by decide) (by decide +kernel) h707

def seg : List (ℕ × ℕ) := [(236, 24), (237, 24), (238, 48), (239, 48), (254, 24), (255, 24), (492, 4), (493, 12), (495, 12), (511, 4), (531, 1), (532, 12), (533, 24), (535, 12), (540, 6), (541, 12), (543, 6), (548, 24), (549, 24), (550, 48), (551, 48), (552, 24), (553, 24), (554, 48), (555, 48), (556, 48), (557, 48), (558, 48), (559, 48), (566, 24), (567, 24), (570, 24)]

theorem segOK : checkSeg 16 perms 236 571 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 236 571 849 445960063 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 445960063)
    (SegSum.cons (w := 24) h236 (SegSum.cons (w := 24) h237 (SegSum.cons (w := 48) h238 (SegSum.cons (w := 48) h239 (SegSum.cons (w := 24) h254 (SegSum.cons (w := 24) h255 (SegSum.cons (w := 4) h492 (SegSum.cons (w := 12) h493 (SegSum.cons (w := 12) h495 (SegSum.cons (w := 4) h511 (SegSum.cons (w := 1) h531 (SegSum.cons (w := 12) h532 (SegSum.cons (w := 24) h533 (SegSum.cons (w := 12) h535 (SegSum.cons (w := 6) h540 (SegSum.cons (w := 12) h541 (SegSum.cons (w := 6) h543 (SegSum.cons (w := 24) h548 (SegSum.cons (w := 24) h549 (SegSum.cons (w := 48) h550 (SegSum.cons (w := 48) h551 (SegSum.cons (w := 24) h552 (SegSum.cons (w := 24) h553 (SegSum.cons (w := 48) h554 (SegSum.cons (w := 48) h555 (SegSum.cons (w := 48) h556 (SegSum.cons (w := 48) h557 (SegSum.cons (w := 48) h558 (SegSum.cons (w := 48) h559 (SegSum.cons (w := 24) h566 (SegSum.cons (w := 24) h567 (SegSum.cons (w := 24) h570 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S2
