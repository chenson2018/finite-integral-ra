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

namespace RACert.S4N1.C0.S31

open RACert RACert.Problem

theorem cover5494 : P.CoversSplit 24 10 5494 0xf0f00000a0a000000000000000000000f0f00000000500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 572, 858, 860, 865, 867, 908, 916, 1202, 1258, 1264]) (by decide +kernel)

theorem c5494_0 : P.sumLeaves 24 5625856 1024 = 1334263 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5494) (lo := 0) (len := 1024) (W := 1334263) check rows elimOK (by decide) (by decide) cover5494 (by decide)
  decide +kernel

theorem h5494 : P.leaf 34 5494 = 1334263 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1334263)]) (.cons c5494_0 (.nil)) (by decide) (by decide))

theorem cover5495 : P.CoversSplit 24 10 5495 0xffffffffaaaaa0a00000000000000000ffffffffaaaaa0a000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffaaaaa0a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [572, 858, 860, 865, 908, 916, 1202, 1209, 1258, 1264]) (ps := [(8, [1217, 1266], [1272])]) (by decide +kernel)

theorem c5495_0 : P.sumLeaves 24 5626880 985 = 8882562 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5495) (lo := 0) (len := 985) (W := 8882562) check rows elimOK (by decide) (by decide) cover5495 (by decide)
  decide +kernel

theorem c5495_1 : P.sumLeaves 24 5627865 39 = 11771612 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5495) (lo := 985) (len := 39) (W := 11771612) check rows elimOK (by decide) (by decide) cover5495 (by decide)
  decide +kernel

theorem h5495 : P.leaf 34 5495 = 20654174 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(985, 8882562), (39, 11771612)]) (.cons c5495_0 (.cons c5495_1 (.nil))) (by decide) (by decide))

theorem h5496 : P.leaf 34 5496 = 0 := by
  exact leaf_contract_zero (ss := [(28, 2, 466), (2, 1, 472), (15, 1, 487), (14, 8, 558), (35, 0, 867), (7, 6, 474), (16, 10, 872), (33, 0, 909), (18, 11, 879), (32, 1, 1264), (27, 1, 572), (29, 1, 473), (34, 1, 572), (8, 1, 1266)]) (q := 1272) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover5497 : P.CoversSplit 24 10 5497 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c5497_0 : P.sumLeaves 24 5628928 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5497) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5497 (by decide)
  decide +kernel

theorem h5497 : P.leaf 34 5497 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5497_0 (.nil)) (by decide) (by decide))

theorem cover5498 : P.CoversSplit 24 10 5498 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c5498_0 : P.sumLeaves 24 5629952 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5498) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5498 (by decide)
  decide +kernel

theorem h5498 : P.leaf 34 5498 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5498_0 (.nil)) (by decide) (by decide))

theorem cover5499 : P.CoversSplit 24 10 5499 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c5499_0 : P.sumLeaves 24 5630976 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5499) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5499 (by decide)
  decide +kernel

theorem h5499 : P.leaf 34 5499 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5499_0 (.nil)) (by decide) (by decide))

theorem cover5500 : P.CoversSplit 24 10 5500 0xc000000080008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 572, 858, 860, 865, 867, 909, 916, 1202, 1209, 1258, 1264]) (by decide +kernel)

theorem c5500_0 : P.sumLeaves 24 5632000 1024 = 213184 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5500) (lo := 0) (len := 1024) (W := 213184) check rows elimOK (by decide) (by decide) cover5500 (by decide)
  decide +kernel

theorem h5500 : P.leaf 34 5500 = 213184 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 213184)]) (.cons c5500_0 (.nil)) (by decide) (by decide))

theorem cover5501 : P.CoversSplit 24 10 5501 0xcc00cc00880080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00880080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 572, 858, 860, 865, 909, 1202, 1209, 1258, 1259, 1264]) (by decide +kernel)

theorem c5501_0 : P.sumLeaves 24 5633024 1024 = 2228662 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5501) (lo := 0) (len := 1024) (W := 2228662) check rows elimOK (by decide) (by decide) cover5501 (by decide)
  decide +kernel

theorem h5501 : P.leaf 34 5501 = 2228662 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2228662)]) (.cons c5501_0 (.nil)) (by decide) (by decide))

theorem cover5502 : P.CoversSplit 24 10 5502 0xf0f00000a0a000000000000000000000f0f00000000500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 572, 858, 860, 865, 867, 916, 1202, 1258, 1264]) (by decide +kernel)

theorem c5502_0 : P.sumLeaves 24 5634048 1024 = 4295091 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5502) (lo := 0) (len := 1024) (W := 4295091) check rows elimOK (by decide) (by decide) cover5502 (by decide)
  decide +kernel

theorem h5502 : P.leaf 34 5502 = 4295091 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4295091)]) (.cons c5502_0 (.nil)) (by decide) (by decide))

theorem cover5503 : P.CoversSplit 24 10 5503 0xffffffffaaaaa0a00000000000000000ffffffffaaaaa0a000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffaaaaa0a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [572, 858, 860, 865, 916, 1202, 1209, 1258, 1264]) (ps := [(8, [1217, 1266], [1272])]) (by decide +kernel)

theorem c5503_0 : P.sumLeaves 24 5635072 985 = 17128677 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5503) (lo := 0) (len := 985) (W := 17128677) check rows elimOK (by decide) (by decide) cover5503 (by decide)
  decide +kernel

theorem c5503_1 : P.sumLeaves 24 5636057 39 = 21475244 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5503) (lo := 985) (len := 39) (W := 21475244) check rows elimOK (by decide) (by decide) cover5503 (by decide)
  decide +kernel

theorem h5503 : P.leaf 34 5503 = 38603921 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(985, 17128677), (39, 21475244)]) (.cons c5503_0 (.cons c5503_1 (.nil))) (by decide) (by decide))

theorem cover5600 : P.CoversSplit 24 10 5600 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c5600_0 : P.sumLeaves 24 5734400 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5600) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5600 (by decide)
  decide +kernel

theorem h5600 : P.leaf 34 5600 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5600_0 (.nil)) (by decide) (by decide))

theorem cover5601 : P.CoversSplit 24 10 5601 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c5601_0 : P.sumLeaves 24 5735424 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5601) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5601 (by decide)
  decide +kernel

theorem h5601 : P.leaf 34 5601 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5601_0 (.nil)) (by decide) (by decide))

theorem cover5603 : P.CoversSplit 24 10 5603 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c5603_0 : P.sumLeaves 24 5737472 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5603) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5603 (by decide)
  decide +kernel

theorem h5603 : P.leaf 34 5603 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5603_0 (.nil)) (by decide) (by decide))

theorem cover5604 : P.CoversSplit 24 10 5604 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c5604_0 : P.sumLeaves 24 5738496 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5604) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5604 (by decide)
  decide +kernel

theorem h5604 : P.leaf 34 5604 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5604_0 (.nil)) (by decide) (by decide))

theorem cover5605 : P.CoversSplit 24 10 5605 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c5605_0 : P.sumLeaves 24 5739520 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5605) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5605 (by decide)
  decide +kernel

theorem h5605 : P.leaf 34 5605 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5605_0 (.nil)) (by decide) (by decide))

theorem cover5607 : P.CoversSplit 24 10 5607 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c5607_0 : P.sumLeaves 24 5741568 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5607) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5607 (by decide)
  decide +kernel

theorem h5607 : P.leaf 34 5607 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5607_0 (.nil)) (by decide) (by decide))

theorem cover5608 : P.CoversSplit 24 10 5608 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c5608_0 : P.sumLeaves 24 5742592 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5608) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5608 (by decide)
  decide +kernel

theorem h5608 : P.leaf 34 5608 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5608_0 (.nil)) (by decide) (by decide))

theorem cover5609 : P.CoversSplit 24 10 5609 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c5609_0 : P.sumLeaves 24 5743616 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5609) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5609 (by decide)
  decide +kernel

theorem h5609 : P.leaf 34 5609 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5609_0 (.nil)) (by decide) (by decide))

theorem cover5611 : P.CoversSplit 24 10 5611 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c5611_0 : P.sumLeaves 24 5745664 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5611) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5611 (by decide)
  decide +kernel

theorem h5611 : P.leaf 34 5611 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5611_0 (.nil)) (by decide) (by decide))

theorem cover5612 : P.CoversSplit 24 10 5612 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c5612_0 : P.sumLeaves 24 5746688 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5612) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5612 (by decide)
  decide +kernel

theorem h5612 : P.leaf 34 5612 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5612_0 (.nil)) (by decide) (by decide))

theorem cover5613 : P.CoversSplit 24 10 5613 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c5613_0 : P.sumLeaves 24 5747712 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5613) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5613 (by decide)
  decide +kernel

theorem h5613 : P.leaf 34 5613 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5613_0 (.nil)) (by decide) (by decide))

theorem cover5615 : P.CoversSplit 24 10 5615 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c5615_0 : P.sumLeaves 24 5749760 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5615) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5615 (by decide)
  decide +kernel

theorem h5615 : P.leaf 34 5615 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5615_0 (.nil)) (by decide) (by decide))

theorem cover5616 : P.CoversSplit 24 10 5616 0xf0000000a000aa00000000000000000000000000000000000000000000000000c000000080088808c0c0000080888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 858, 860, 865, 867, 909, 1202, 1258, 1601]) (by decide +kernel)

noncomputable def f5616 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (5750784 + i)

theorem c5616_0 : rowSum f5616 0 1024 = 7058 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5616) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover5616 (by decide)
  decide +kernel

theorem sum5616 : rowSum f5616 0 1024 = 7058 :=
  c5616_0

theorem h5616 : P.leaf 34 5616 = 7058 :=
  leaf_weighted (k := 24) (d := 10) (H := 5616) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 5616) (by decide) (by decide +kernel)) sum5616

theorem cover5617 : P.CoversSplit 24 10 5617 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c5617_0 : P.sumLeaves 24 5751808 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5617) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5617 (by decide)
  decide +kernel

theorem h5617 : P.leaf 34 5617 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5617_0 (.nil)) (by decide) (by decide))

theorem cover5619 : P.CoversSplit 24 10 5619 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c5619_0 : P.sumLeaves 24 5753856 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5619) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5619 (by decide)
  decide +kernel

theorem h5619 : P.leaf 34 5619 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5619_0 (.nil)) (by decide) (by decide))

theorem cover5620 : P.CoversSplit 24 10 5620 0xf0000000a000aa00000000000000000000000000000000000000000000000000c000000080088808c0c00000808888880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 858, 860, 865, 867, 909, 1202, 1258, 1601]) (by decide +kernel)

noncomputable def f5620 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (5754880 + i)

theorem c5620_0 : rowSum f5620 0 1024 = 266200 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5620) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover5620 (by decide)
  decide +kernel

theorem sum5620 : rowSum f5620 0 1024 = 266200 :=
  c5620_0

theorem h5620 : P.leaf 34 5620 = 266200 :=
  leaf_weighted (k := 24) (d := 10) (H := 5620) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 5620) (by decide) (by decide +kernel)) sum5620

theorem cover5621 : P.CoversSplit 24 10 5621 0xff00ff00aa00a000000000000000000000000000000000000000000000000000cc00cc0088008000000000000000000000000000000000000000000000000000ff00ff00aa00a0000000000000000000000000000000000000000000000000000003000300000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 858, 860, 865, 866, 909, 916, 1202, 1258, 1601]) (by decide +kernel)

theorem c5621_0 : P.sumLeaves 24 5755904 1024 = 3641858 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5621) (lo := 0) (len := 1024) (W := 3641858) check rows elimOK (by decide) (by decide) cover5621 (by decide)
  decide +kernel

theorem h5621 : P.leaf 34 5621 = 3641858 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3641858)]) (.cons c5621_0 (.nil)) (by decide) (by decide))

theorem cover5623 : P.CoversSplit 24 10 5623 0xffffffffaaaaaaaaffff0000aaaa0000ffffffffaaaaaaaaffff0000aaaa0000cccccccc88888888cccc000088880000cccccccc88888888cccc000088880000ffffffffaaaaaaaaffff0000aaaa0000ffffffffaaaaaaaaffff0000aaaa0000cccccccc88888888cccc000088880000cccccccc88888888cccc000088880000 :=
  coversSplit check rows (by decide) (by decide) (xs := [858, 860, 865, 866, 916, 1202, 1258, 1601]) (by decide +kernel)

noncomputable def f5623 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (5757952 + i)

theorem c5623_0 : rowSum f5623 0 407 = 11212024 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5623) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover5623 (by decide)
  decide +kernel

theorem c5623_1 : rowSum f5623 407 355 = 47036682 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5623) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover5623 (by decide)
  decide +kernel

theorem c5623_2 : rowSum f5623 762 262 = 31383416 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5623) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover5623 (by decide)
  decide +kernel

theorem sum5623 : rowSum f5623 0 1024 = 89632122 :=
  rowSum_append (F := f5623) (lo := 0) (n := 407) (m := 617) (A := 11212024) (B := 78420098) c5623_0 (rowSum_append (F := f5623) (lo := 407) (n := 355) (m := 262) (A := 47036682) (B := 31383416) c5623_1 (c5623_2))

theorem h5623 : P.leaf 34 5623 = 89632122 :=
  leaf_weighted (k := 24) (d := 10) (H := 5623) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 5623) (by decide) (by decide +kernel)) sum5623

theorem cover5624 : P.CoversSplit 24 10 5624 0xf0000000a000aa00000000000000000000000000000000000000000000000000c000000080088808c0c0000080888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 858, 860, 865, 867, 909, 1202, 1258, 1601]) (by decide +kernel)

noncomputable def f5624 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (5758976 + i)

theorem c5624_0 : rowSum f5624 0 1024 = 55770 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5624) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover5624 (by decide)
  decide +kernel

theorem sum5624 : rowSum f5624 0 1024 = 55770 :=
  c5624_0

theorem h5624 : P.leaf 34 5624 = 55770 :=
  leaf_weighted (k := 24) (d := 10) (H := 5624) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 5624) (by decide) (by decide +kernel)) sum5624

theorem cover5625 : P.CoversSplit 24 10 5625 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c5625_0 : P.sumLeaves 24 5760000 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5625) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5625 (by decide)
  decide +kernel

theorem h5625 : P.leaf 34 5625 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5625_0 (.nil)) (by decide) (by decide))

theorem cover5627 : P.CoversSplit 24 10 5627 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c5627_0 : P.sumLeaves 24 5762048 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5627) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5627 (by decide)
  decide +kernel

theorem h5627 : P.leaf 34 5627 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5627_0 (.nil)) (by decide) (by decide))

theorem cover5628 : P.CoversSplit 24 10 5628 0xf0000000a000aa00000000000000000000000000000000000000000000000000c000000080088808c0c00000808888880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 858, 860, 865, 867, 909, 1202, 1258, 1601]) (by decide +kernel)

noncomputable def f5628 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (5763072 + i)

theorem c5628_0 : rowSum f5628 0 1024 = 1145902 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5628) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover5628 (by decide)
  decide +kernel

theorem sum5628 : rowSum f5628 0 1024 = 1145902 :=
  c5628_0

theorem h5628 : P.leaf 34 5628 = 1145902 :=
  leaf_weighted (k := 24) (d := 10) (H := 5628) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 5628) (by decide) (by decide +kernel)) sum5628

def seg : List (ℕ × ℕ) := [(5494, 48), (5495, 48), (5496, 48), (5497, 48), (5498, 48), (5499, 48), (5500, 48), (5501, 48), (5502, 48), (5503, 48), (5600, 24), (5601, 48), (5603, 24), (5604, 24), (5605, 48), (5607, 24), (5608, 24), (5609, 48), (5611, 24), (5612, 24), (5613, 48), (5615, 24), (5616, 24), (5617, 48), (5619, 24), (5620, 24), (5621, 48), (5623, 24), (5624, 24), (5625, 48), (5627, 24), (5628, 24)]

theorem segOK : checkSeg 16 perms 5494 5629 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 5494 5629 1176 5593184592 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 5593184592)
    (SegSum.cons (w := 48) h5494 (SegSum.cons (w := 48) h5495 (SegSum.cons (w := 48) h5496 (SegSum.cons (w := 48) h5497 (SegSum.cons (w := 48) h5498 (SegSum.cons (w := 48) h5499 (SegSum.cons (w := 48) h5500 (SegSum.cons (w := 48) h5501 (SegSum.cons (w := 48) h5502 (SegSum.cons (w := 48) h5503 (SegSum.cons (w := 24) h5600 (SegSum.cons (w := 48) h5601 (SegSum.cons (w := 24) h5603 (SegSum.cons (w := 24) h5604 (SegSum.cons (w := 48) h5605 (SegSum.cons (w := 24) h5607 (SegSum.cons (w := 24) h5608 (SegSum.cons (w := 48) h5609 (SegSum.cons (w := 24) h5611 (SegSum.cons (w := 24) h5612 (SegSum.cons (w := 48) h5613 (SegSum.cons (w := 24) h5615 (SegSum.cons (w := 24) h5616 (SegSum.cons (w := 48) h5617 (SegSum.cons (w := 24) h5619 (SegSum.cons (w := 24) h5620 (SegSum.cons (w := 48) h5621 (SegSum.cons (w := 24) h5623 (SegSum.cons (w := 24) h5624 (SegSum.cons (w := 48) h5625 (SegSum.cons (w := 24) h5627 (SegSum.cons (w := 24) h5628 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S31
