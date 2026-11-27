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

namespace RACert.S4N1.C0.S29

open RACert RACert.Problem

theorem h5357 : P.leaf 34 5357 = 0 := by
  exact leaf_contract_zero (ss := [(30, 1, 466), (4, 1, 508), (35, 0, 867), (18, 1, 487), (16, 1, 872), (33, 0, 909), (11, 1, 879)]) (q := 1272) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover5358 : P.CoversSplit 24 10 5358 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c5358_0 : P.sumLeaves 24 5486592 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5358) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5358 (by decide)
  decide +kernel

theorem h5358 : P.leaf 34 5358 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5358_0 (.nil)) (by decide) (by decide))

theorem cover5359 : P.CoversSplit 24 10 5359 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c5359_0 : P.sumLeaves 24 5487616 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5359) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5359 (by decide)
  decide +kernel

theorem h5359 : P.leaf 34 5359 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5359_0 (.nil)) (by decide) (by decide))

theorem h5361 : P.leaf 34 5361 = 0 := by
  exact leaf_contract_zero (ss := [(8, 0, 475), (6, 1, 478), (12, 1, 478), (11, 1, 459), (14, 0, 487), (33, 1, 482)]) (q := 488) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover5362 : P.CoversSplit 24 10 5362 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c5362_0 : P.sumLeaves 24 5490688 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5362) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5362 (by decide)
  decide +kernel

theorem h5362 : P.leaf 34 5362 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5362_0 (.nil)) (by decide) (by decide))

theorem cover5363 : P.CoversSplit 24 10 5363 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c5363_0 : P.sumLeaves 24 5491712 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5363) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5363 (by decide)
  decide +kernel

theorem h5363 : P.leaf 34 5363 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5363_0 (.nil)) (by decide) (by decide))

theorem cover5364 : P.CoversSplit 24 10 5364 0xf0000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 573, 858, 860, 865, 867, 909, 1202, 1210, 1259]) (by decide +kernel)

theorem c5364_0 : P.sumLeaves 24 5492736 1024 = 40392 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5364) (lo := 0) (len := 1024) (W := 40392) check rows elimOK (by decide) (by decide) cover5364 (by decide)
  decide +kernel

theorem h5364 : P.leaf 34 5364 = 40392 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 40392)]) (.cons c5364_0 (.nil)) (by decide) (by decide))

theorem cover5365 : P.CoversSplit 24 10 5365 0xff00ff00aa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 573, 858, 860, 865, 866, 867, 909, 916, 1202, 1210, 1259]) (by decide +kernel)

theorem c5365_0 : P.sumLeaves 24 5493760 1024 = 323584 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5365) (lo := 0) (len := 1024) (W := 323584) check rows elimOK (by decide) (by decide) cover5365 (by decide)
  decide +kernel

theorem h5365 : P.leaf 34 5365 = 323584 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 323584)]) (.cons c5365_0 (.nil)) (by decide) (by decide))

theorem cover5366 : P.CoversSplit 24 10 5366 0xf0f00000a0a000000000000000000000f0f00000000500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 573, 858, 860, 865, 867, 908, 916, 1202, 1210, 1259, 1264]) (by decide +kernel)

theorem c5366_0 : P.sumLeaves 24 5494784 1024 = 904560 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5366) (lo := 0) (len := 1024) (W := 904560) check rows elimOK (by decide) (by decide) cover5366 (by decide)
  decide +kernel

theorem h5366 : P.leaf 34 5366 = 904560 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 904560)]) (.cons c5366_0 (.nil)) (by decide) (by decide))

theorem cover5367 : P.CoversSplit 24 10 5367 0xffffffffaaaa00000000000000000000ffffffffaaaa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [573, 858, 860, 865, 866, 867, 916, 1202, 1210, 1259, 1264]) (by decide +kernel)

theorem c5367_0 : P.sumLeaves 24 5495808 1024 = 10175096 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5367) (lo := 0) (len := 1024) (W := 10175096) check rows elimOK (by decide) (by decide) cover5367 (by decide)
  decide +kernel

theorem h5367 : P.leaf 34 5367 = 10175096 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 10175096)]) (.cons c5367_0 (.nil)) (by decide) (by decide))

theorem h5368 : P.leaf 34 5368 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 466), (35, 14, 487), (28, 1, 508), (14, 0, 867), (15, 1, 486), (16, 10, 872), (33, 0, 909), (21, 0, 874), (18, 11, 879), (20, 1, 880), (12, 1, 951), (31, 1, 860), (30, 1, 858), (34, 1, 965), (29, 1, 865), (27, 1, 573), (32, 1, 865), (8, 0, 972), (5, 1, 411), (4, 1, 410), (9, 1, 678)]) (q := 1272) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem h5369 : P.leaf 34 5369 = 0 := by
  exact leaf_contract_zero (ss := [(35, 14, 487), (14, 0, 867), (16, 1, 872), (33, 0, 909), (8, 0, 874), (5, 1, 433), (18, 11, 475), (20, 1, 482), (21, 0, 488), (29, 15, 558), (12, 1, 608), (34, 1, 622), (7, 1, 628), (6, 1, 460), (10, 1, 811), (15, 1, 865), (27, 1, 573), (9, 1, 678), (32, 1, 865), (13, 1, 971), (31, 1, 1217), (11, 1, 1265)]) (q := 1272) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover5370 : P.CoversSplit 24 10 5370 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c5370_0 : P.sumLeaves 24 5498880 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5370) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5370 (by decide)
  decide +kernel

theorem h5370 : P.leaf 34 5370 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5370_0 (.nil)) (by decide) (by decide))

theorem cover5371 : P.CoversSplit 24 10 5371 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c5371_0 : P.sumLeaves 24 5499904 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5371) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5371 (by decide)
  decide +kernel

theorem h5371 : P.leaf 34 5371 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5371_0 (.nil)) (by decide) (by decide))

theorem cover5372 : P.CoversSplit 24 10 5372 0xf0000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 573, 858, 860, 865, 867, 909, 1202, 1210, 1258, 1259]) (by decide +kernel)

theorem c5372_0 : P.sumLeaves 24 5500928 1024 = 309192 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5372) (lo := 0) (len := 1024) (W := 309192) check rows elimOK (by decide) (by decide) cover5372 (by decide)
  decide +kernel

theorem h5372 : P.leaf 34 5372 = 309192 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 309192)]) (.cons c5372_0 (.nil)) (by decide) (by decide))

theorem cover5373 : P.CoversSplit 24 10 5373 0xff00ff00aa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 573, 858, 860, 865, 867, 909, 916, 1202, 1210, 1258, 1259]) (by decide +kernel)

theorem c5373_0 : P.sumLeaves 24 5501952 1024 = 1862640 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5373) (lo := 0) (len := 1024) (W := 1862640) check rows elimOK (by decide) (by decide) cover5373 (by decide)
  decide +kernel

theorem h5373 : P.leaf 34 5373 = 1862640 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1862640)]) (.cons c5373_0 (.nil)) (by decide) (by decide))

theorem cover5374 : P.CoversSplit 24 10 5374 0xf0f00000a0a000000000000000000000f0f00000000500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 573, 858, 860, 865, 867, 916, 1202, 1210, 1258, 1259, 1264]) (by decide +kernel)

theorem c5374_0 : P.sumLeaves 24 5502976 1024 = 4238222 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5374) (lo := 0) (len := 1024) (W := 4238222) check rows elimOK (by decide) (by decide) cover5374 (by decide)
  decide +kernel

theorem h5374 : P.leaf 34 5374 = 4238222 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4238222)]) (.cons c5374_0 (.nil)) (by decide) (by decide))

theorem cover5375 : P.CoversSplit 24 10 5375 0xffffffffaaaa00000000000000000000ffffffffaaaa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [573, 858, 860, 865, 867, 916, 1202, 1210, 1258, 1259, 1264]) (by decide +kernel)

theorem c5375_0 : P.sumLeaves 24 5504000 1024 = 20566456 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5375) (lo := 0) (len := 1024) (W := 20566456) check rows elimOK (by decide) (by decide) cover5375 (by decide)
  decide +kernel

theorem h5375 : P.leaf 34 5375 = 20566456 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 20566456)]) (.cons c5375_0 (.nil)) (by decide) (by decide))

theorem cover5440 : P.CoversSplit 24 10 5440 0x800000000000040000000000000000000000000000000000000000000000000000000000000100010020000000010000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 516, 522, 523, 565, 858, 865, 1202, 1209, 1258, 1259]) (by decide +kernel)

noncomputable def f5440 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (5570560 + i)

theorem c5440_0 : rowSum f5440 0 1024 = 352 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5440) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover5440 (by decide)
  decide +kernel

theorem sum5440 : rowSum f5440 0 1024 = 352 :=
  c5440_0

theorem h5440 : P.leaf 34 5440 = 352 :=
  leaf_weighted (k := 24) (d := 10) (H := 5440) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 5440) (by decide) (by decide +kernel)) sum5440

theorem cover5441 : P.CoversSplit 24 10 5441 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [523]) (by decide +kernel)

theorem c5441_0 : P.sumLeaves 24 5571584 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5441) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5441 (by decide)
  decide +kernel

theorem h5441 : P.leaf 34 5441 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5441_0 (.nil)) (by decide) (by decide))

theorem cover5443 : P.CoversSplit 24 10 5443 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [523]) (by decide +kernel)

theorem c5443_0 : P.sumLeaves 24 5573632 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5443) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5443 (by decide)
  decide +kernel

theorem h5443 : P.leaf 34 5443 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5443_0 (.nil)) (by decide) (by decide))

theorem cover5444 : P.CoversSplit 24 10 5444 0x800000000000040000000000000000000000000000000000000000000000000000000000000100010020000000010000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 473, 515, 516, 522, 523, 565, 572, 858, 860, 865, 916]) (by decide +kernel)

noncomputable def f5444 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (5574656 + i)

theorem c5444_0 : rowSum f5444 0 1024 = 2184 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5444) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover5444 (by decide)
  decide +kernel

theorem sum5444 : rowSum f5444 0 1024 = 2184 :=
  c5444_0

theorem h5444 : P.leaf 34 5444 = 2184 :=
  leaf_weighted (k := 24) (d := 10) (H := 5444) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 5444) (by decide) (by decide +kernel)) sum5444

theorem cover5445 : P.CoversSplit 24 10 5445 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [523]) (by decide +kernel)

theorem c5445_0 : P.sumLeaves 24 5575680 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5445) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5445 (by decide)
  decide +kernel

theorem h5445 : P.leaf 34 5445 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5445_0 (.nil)) (by decide) (by decide))

theorem cover5447 : P.CoversSplit 24 10 5447 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [523]) (by decide +kernel)

theorem c5447_0 : P.sumLeaves 24 5577728 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5447) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5447 (by decide)
  decide +kernel

theorem h5447 : P.leaf 34 5447 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5447_0 (.nil)) (by decide) (by decide))

theorem cover5448 : P.CoversSplit 24 10 5448 0x800000000000040000000000000000000000000000000000000000000000000000000000000100010020000000010000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 473, 515, 516, 522, 523, 565, 858, 865, 1202, 1209, 1258, 1259]) (by decide +kernel)

noncomputable def f5448 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (5578752 + i)

theorem c5448_0 : rowSum f5448 0 1024 = 2232 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5448) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover5448 (by decide)
  decide +kernel

theorem sum5448 : rowSum f5448 0 1024 = 2232 :=
  c5448_0

theorem h5448 : P.leaf 34 5448 = 2232 :=
  leaf_weighted (k := 24) (d := 10) (H := 5448) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 5448) (by decide) (by decide +kernel)) sum5448

theorem cover5449 : P.CoversSplit 24 10 5449 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [523]) (by decide +kernel)

theorem c5449_0 : P.sumLeaves 24 5579776 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5449) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5449 (by decide)
  decide +kernel

theorem h5449 : P.leaf 34 5449 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5449_0 (.nil)) (by decide) (by decide))

theorem cover5451 : P.CoversSplit 24 10 5451 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [523]) (by decide +kernel)

theorem c5451_0 : P.sumLeaves 24 5581824 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5451) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5451 (by decide)
  decide +kernel

theorem h5451 : P.leaf 34 5451 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5451_0 (.nil)) (by decide) (by decide))

theorem cover5452 : P.CoversSplit 24 10 5452 0x800000000000040000000000000000000000000000000000000000000000000000000000000100010020000000010000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 473, 515, 516, 522, 523, 565, 572, 858, 860, 865, 916]) (by decide +kernel)

noncomputable def f5452 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (5582848 + i)

theorem c5452_0 : rowSum f5452 0 1024 = 17856 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5452) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover5452 (by decide)
  decide +kernel

theorem sum5452 : rowSum f5452 0 1024 = 17856 :=
  c5452_0

theorem h5452 : P.leaf 34 5452 = 17856 :=
  leaf_weighted (k := 24) (d := 10) (H := 5452) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 5452) (by decide) (by decide +kernel)) sum5452

theorem cover5453 : P.CoversSplit 24 10 5453 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [523]) (by decide +kernel)

theorem c5453_0 : P.sumLeaves 24 5583872 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5453) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5453 (by decide)
  decide +kernel

theorem h5453 : P.leaf 34 5453 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5453_0 (.nil)) (by decide) (by decide))

theorem cover5455 : P.CoversSplit 24 10 5455 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [523]) (by decide +kernel)

theorem c5455_0 : P.sumLeaves 24 5585920 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5455) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5455 (by decide)
  decide +kernel

theorem h5455 : P.leaf 34 5455 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5455_0 (.nil)) (by decide) (by decide))

theorem h5456 : P.leaf 34 5456 = 0 := by
  exact leaf_contract_zero (ss := [(28, 2, 466), (7, 6, 467), (29, 2, 472), (6, 1, 479), (15, 2, 486), (14, 8, 509), (8, 1, 482), (2, 1, 468), (26, 1, 465), (27, 1, 473), (35, 0, 867), (34, 5, 523), (16, 10, 872), (33, 0, 909), (31, 5, 565), (18, 11, 879), (5, 1, 1210), (3, 1, 409), (4, 1, 410), (10, 1, 458), (11, 1, 459), (12, 1, 460), (17, 1, 537), (19, 1, 586), (30, 1, 858), (32, 1, 865)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover5457 : P.CoversSplit 24 10 5457 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c5457_0 : P.sumLeaves 24 5587968 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5457) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5457 (by decide)
  decide +kernel

theorem h5457 : P.leaf 34 5457 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5457_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(5357, 48), (5358, 48), (5359, 48), (5361, 24), (5362, 48), (5363, 48), (5364, 48), (5365, 48), (5366, 48), (5367, 48), (5368, 48), (5369, 48), (5370, 48), (5371, 48), (5372, 48), (5373, 48), (5374, 48), (5375, 48), (5440, 12), (5441, 24), (5443, 12), (5444, 12), (5445, 24), (5447, 12), (5448, 12), (5449, 24), (5451, 12), (5452, 12), (5453, 24), (5455, 12), (5456, 24), (5457, 48)]

theorem segOK : checkSeg 16 perms 5357 5459 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 5357 5459 1104 1844438304 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1844438304)
    (SegSum.cons (w := 48) h5357 (SegSum.cons (w := 48) h5358 (SegSum.cons (w := 48) h5359 (SegSum.cons (w := 24) h5361 (SegSum.cons (w := 48) h5362 (SegSum.cons (w := 48) h5363 (SegSum.cons (w := 48) h5364 (SegSum.cons (w := 48) h5365 (SegSum.cons (w := 48) h5366 (SegSum.cons (w := 48) h5367 (SegSum.cons (w := 48) h5368 (SegSum.cons (w := 48) h5369 (SegSum.cons (w := 48) h5370 (SegSum.cons (w := 48) h5371 (SegSum.cons (w := 48) h5372 (SegSum.cons (w := 48) h5373 (SegSum.cons (w := 48) h5374 (SegSum.cons (w := 48) h5375 (SegSum.cons (w := 12) h5440 (SegSum.cons (w := 24) h5441 (SegSum.cons (w := 12) h5443 (SegSum.cons (w := 12) h5444 (SegSum.cons (w := 24) h5445 (SegSum.cons (w := 12) h5447 (SegSum.cons (w := 12) h5448 (SegSum.cons (w := 24) h5449 (SegSum.cons (w := 12) h5451 (SegSum.cons (w := 12) h5452 (SegSum.cons (w := 24) h5453 (SegSum.cons (w := 12) h5455 (SegSum.cons (w := 24) h5456 (SegSum.cons (w := 48) h5457 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S29
