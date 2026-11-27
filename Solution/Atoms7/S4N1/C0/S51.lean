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

namespace RACert.S4N1.C0.S51

open RACert RACert.Problem

theorem cover7608 : P.CoversSplit 24 10 7608 0xf0000000000000000000000000000000a0000000000000000000000000000000c000000000000000c00000000000000080000000000000008000000000000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000c00000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 517, 858, 865, 867, 909, 916, 1202, 1209, 1308, 1601]) (by decide +kernel)

theorem c7608_0 : P.sumLeaves 24 7790592 1024 = 637680 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7608) (lo := 0) (len := 1024) (W := 637680) check rows elimOK (by decide) (by decide) cover7608 (by decide)
  decide +kernel

theorem h7608 : P.leaf 34 7608 = 637680 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 637680)]) (.cons c7608_0 (.nil)) (by decide) (by decide))

theorem cover7609 : P.CoversSplit 24 10 7609 0xff000000000000000000000000000000ff000000000000000000000000000000cc030000000000000000000000000000cc030000000000000000000000000000ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 517, 858, 865, 867, 916, 1202, 1209, 1210, 1308, 1601]) (by decide +kernel)

theorem c7609_0 : P.sumLeaves 24 7791616 1024 = 7229070 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7609) (lo := 0) (len := 1024) (W := 7229070) check rows elimOK (by decide) (by decide) cover7609 (by decide)
  decide +kernel

theorem h7609 : P.leaf 34 7609 = 7229070 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 7229070)]) (.cons c7609_0 (.nil)) (by decide) (by decide))

theorem cover7610 : P.CoversSplit 24 10 7610 0xf0f0000000000000f0f0000000000000a0a0000000000000a0a0000000000000c0f0000000000000c00000000000000080a00000000000008000000000000000f0f0000000000000f0f000000000000000000000000000000000000000000000c0f0000000000000c00000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 517, 858, 865, 867, 909, 1209, 1308, 1601]) (by decide +kernel)

theorem c7610_0 : P.sumLeaves 24 7792640 1024 = 5528476 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7610) (lo := 0) (len := 1024) (W := 5528476) check rows elimOK (by decide) (by decide) cover7610 (by decide)
  decide +kernel

theorem h7610 : P.leaf 34 7610 = 5528476 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5528476)]) (.cons c7610_0 (.nil)) (by decide) (by decide))

theorem cover7611 : P.CoversSplit 24 10 7611 0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ccfc000000000000cc00000000000000ccfc000000000000cc00000000000000ffff000000000000ffff00000000000000000000000000000000000000000000ccfc000000000000cc0000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 858, 865, 867, 916, 1202, 1209, 1210, 1308, 1601]) (by decide +kernel)

theorem c7611_0 : P.sumLeaves 24 7793664 886 = 10886334 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7611) (lo := 0) (len := 886) (W := 10886334) check rows elimOK (by decide) (by decide) cover7611 (by decide)
  decide +kernel

theorem c7611_1 : P.sumLeaves 24 7794550 138 = 18640214 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7611) (lo := 886) (len := 138) (W := 18640214) check rows elimOK (by decide) (by decide) cover7611 (by decide)
  decide +kernel

theorem h7611 : P.leaf 34 7611 = 29526548 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(886, 10886334), (138, 18640214)]) (.cons c7611_0 (.cons c7611_1 (.nil))) (by decide) (by decide))

theorem cover7612 : P.CoversSplit 24 10 7612 0xf0000000000000000000000000000000a0000000000000000000000000000000c000000000000000c00000000000000080000000000000008000000000000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 517, 858, 865, 916, 1202, 1209, 1308, 1601]) (by decide +kernel)

theorem c7612_0 : P.sumLeaves 24 7794688 1024 = 2557588 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7612) (lo := 0) (len := 1024) (W := 2557588) check rows elimOK (by decide) (by decide) cover7612 (by decide)
  decide +kernel

theorem h7612 : P.leaf 34 7612 = 2557588 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2557588)]) (.cons c7612_0 (.nil)) (by decide) (by decide))

theorem cover7613 : P.CoversSplit 24 10 7613 0xff000000000000000000000000000000ff000000000000000000000000000000cc030000000000000000000000000000cc030000000000000000000000000000ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 517, 858, 865, 916, 1202, 1209, 1210, 1251, 1308, 1601]) (by decide +kernel)

theorem c7613_0 : P.sumLeaves 24 7795712 1024 = 14700672 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7613) (lo := 0) (len := 1024) (W := 14700672) check rows elimOK (by decide) (by decide) cover7613 (by decide)
  decide +kernel

theorem h7613 : P.leaf 34 7613 = 14700672 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 14700672)]) (.cons c7613_0 (.nil)) (by decide) (by decide))

theorem cover7614 : P.CoversSplit 24 10 7614 0xf0f0000000000000f0f0000000000000a0a0000000000000a0a0000000000000c0f0000000000000c00000000000000080a00000000000008000000000000000f0f0000000000000f0f000000000000000000000000000000000000000000000c0f0000000000000c00000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 517, 858, 865, 1209, 1308, 1601]) (by decide +kernel)

theorem c7614_0 : P.sumLeaves 24 7796736 1024 = 19055250 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7614) (lo := 0) (len := 1024) (W := 19055250) check rows elimOK (by decide) (by decide) cover7614 (by decide)
  decide +kernel

theorem h7614 : P.leaf 34 7614 = 19055250 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 19055250)]) (.cons c7614_0 (.nil)) (by decide) (by decide))

theorem cover7615 : P.CoversSplit 24 10 7615 0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ccfc000000000000cc00000000000000ccfc000000000000cc00000000000000ffff000000000000ffff00000000000000000000000000000000000000000000ccfc000000000000cc0000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 858, 865, 1202, 1209, 1210, 1251, 1258, 1308, 1601]) (by decide +kernel)

theorem c7615_0 : P.sumLeaves 24 7797760 886 = 26503458 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7615) (lo := 0) (len := 886) (W := 26503458) check rows elimOK (by decide) (by decide) cover7615 (by decide)
  decide +kernel

theorem c7615_1 : P.sumLeaves 24 7798646 138 = 39677952 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7615) (lo := 886) (len := 138) (W := 39677952) check rows elimOK (by decide) (by decide) cover7615 (by decide)
  decide +kernel

theorem h7615 : P.leaf 34 7615 = 66181410 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(886, 26503458), (138, 39677952)]) (.cons c7615_0 (.cons c7615_1 (.nil))) (by decide) (by decide))

theorem cover7616 : P.CoversSplit 24 10 7616 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c7616_0 : P.sumLeaves 24 7798784 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7616) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7616 (by decide)
  decide +kernel

theorem h7616 : P.leaf 34 7616 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7616_0 (.nil)) (by decide) (by decide))

theorem cover7617 : P.CoversSplit 24 10 7617 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 523, 858, 865, 916, 1209, 1258, 1272]) (by decide +kernel)

theorem c7617_0 : P.sumLeaves 24 7799808 1024 = 50248 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7617) (lo := 0) (len := 1024) (W := 50248) check rows elimOK (by decide) (by decide) cover7617 (by decide)
  decide +kernel

theorem h7617 : P.leaf 34 7617 = 50248 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 50248)]) (.cons c7617_0 (.nil)) (by decide) (by decide))

theorem cover7619 : P.CoversSplit 24 10 7619 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 516, 522, 523, 858, 865, 1209, 1217, 1258, 1272]) (by decide +kernel)

noncomputable def f7619 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (7801856 + i)

theorem c7619_0 : rowSum f7619 0 1024 = 490484 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 7619) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover7619 (by decide)
  decide +kernel

theorem sum7619 : rowSum f7619 0 1024 = 490484 :=
  c7619_0

theorem h7619 : P.leaf 34 7619 = 490484 :=
  leaf_weighted (k := 24) (d := 10) (H := 7619) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 7619) (by decide) (by decide +kernel)) sum7619

theorem cover7620 : P.CoversSplit 24 10 7620 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c7620_0 : P.sumLeaves 24 7802880 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7620) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7620 (by decide)
  decide +kernel

theorem h7620 : P.leaf 34 7620 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7620_0 (.nil)) (by decide) (by decide))

theorem cover7621 : P.CoversSplit 24 10 7621 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 523, 858, 865, 916, 1209, 1258, 1272]) (by decide +kernel)

theorem c7621_0 : P.sumLeaves 24 7803904 1024 = 552556 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7621) (lo := 0) (len := 1024) (W := 552556) check rows elimOK (by decide) (by decide) cover7621 (by decide)
  decide +kernel

theorem h7621 : P.leaf 34 7621 = 552556 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 552556)]) (.cons c7621_0 (.nil)) (by decide) (by decide))

theorem cover7623 : P.CoversSplit 24 10 7623 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 516, 522, 523, 858, 865, 1209, 1217, 1258, 1272]) (by decide +kernel)

noncomputable def f7623 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (7805952 + i)

theorem c7623_0 : rowSum f7623 0 1024 = 2079224 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 7623) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover7623 (by decide)
  decide +kernel

theorem sum7623 : rowSum f7623 0 1024 = 2079224 :=
  c7623_0

theorem h7623 : P.leaf 34 7623 = 2079224 :=
  leaf_weighted (k := 24) (d := 10) (H := 7623) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 7623) (by decide) (by decide +kernel)) sum7623

theorem cover7624 : P.CoversSplit 24 10 7624 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c7624_0 : P.sumLeaves 24 7806976 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7624) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7624 (by decide)
  decide +kernel

theorem h7624 : P.leaf 34 7624 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7624_0 (.nil)) (by decide) (by decide))

theorem cover7625 : P.CoversSplit 24 10 7625 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 523, 858, 865, 916, 1209, 1258, 1272]) (by decide +kernel)

theorem c7625_0 : P.sumLeaves 24 7808000 1024 = 286307 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7625) (lo := 0) (len := 1024) (W := 286307) check rows elimOK (by decide) (by decide) cover7625 (by decide)
  decide +kernel

theorem h7625 : P.leaf 34 7625 = 286307 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 286307)]) (.cons c7625_0 (.nil)) (by decide) (by decide))

theorem cover7627 : P.CoversSplit 24 10 7627 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 516, 522, 523, 858, 865, 1209, 1217, 1258, 1272]) (by decide +kernel)

noncomputable def f7627 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (7810048 + i)

theorem c7627_0 : rowSum f7627 0 1024 = 521148 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 7627) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover7627 (by decide)
  decide +kernel

theorem sum7627 : rowSum f7627 0 1024 = 521148 :=
  c7627_0

theorem h7627 : P.leaf 34 7627 = 521148 :=
  leaf_weighted (k := 24) (d := 10) (H := 7627) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 7627) (by decide) (by decide +kernel)) sum7627

theorem cover7628 : P.CoversSplit 24 10 7628 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c7628_0 : P.sumLeaves 24 7811072 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7628) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7628 (by decide)
  decide +kernel

theorem h7628 : P.leaf 34 7628 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7628_0 (.nil)) (by decide) (by decide))

theorem cover7629 : P.CoversSplit 24 10 7629 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 523, 858, 865, 916, 1209, 1258, 1272]) (by decide +kernel)

theorem c7629_0 : P.sumLeaves 24 7812096 1024 = 1188401 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7629) (lo := 0) (len := 1024) (W := 1188401) check rows elimOK (by decide) (by decide) cover7629 (by decide)
  decide +kernel

theorem h7629 : P.leaf 34 7629 = 1188401 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1188401)]) (.cons c7629_0 (.nil)) (by decide) (by decide))

theorem cover7631 : P.CoversSplit 24 10 7631 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 516, 522, 523, 858, 865, 1209, 1217, 1258, 1272]) (by decide +kernel)

noncomputable def f7631 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (7814144 + i)

theorem c7631_0 : rowSum f7631 0 1024 = 2224851 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 7631) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover7631 (by decide)
  decide +kernel

theorem sum7631 : rowSum f7631 0 1024 = 2224851 :=
  c7631_0

theorem h7631 : P.leaf 34 7631 = 2224851 :=
  leaf_weighted (k := 24) (d := 10) (H := 7631) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 7631) (by decide) (by decide +kernel)) sum7631

theorem cover7633 : P.CoversSplit 24 10 7633 0xff000000000000000000000000000000ff000000000000000000000000000000cc030000000000000000000000000000cc030000000000000000000000000000ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 516, 858, 865, 866, 867, 916, 1202, 1209, 1210, 1251, 1601]) (ps := [(8, [1272], [1266])]) (by decide +kernel)

theorem c7633_0 : P.sumLeaves 24 7816192 1024 = 1192068 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7633) (lo := 0) (len := 1024) (W := 1192068) check rows elimOK (by decide) (by decide) cover7633 (by decide)
  decide +kernel

theorem h7633 : P.leaf 34 7633 = 1192068 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1192068)]) (.cons c7633_0 (.nil)) (by decide) (by decide))

theorem cover7634 : P.CoversSplit 24 10 7634 0xf0f0000000000000f0f0000000000000a0a0000000000000a0a0000000000000c0f0000000000000c00000000000000080a00000000000008000000000000000f0f0000000000000f0f000000000000000000000000000000000000000000000c0f0000000000000c00000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 516, 858, 865, 866, 867, 909, 1210, 1251, 1601, 1609]) (ps := [(8, [1272], [1266])]) (by decide +kernel)

theorem c7634_0 : P.sumLeaves 24 7817216 192 = 6976 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7634) (lo := 0) (len := 192) (W := 6976) check rows elimOK (by decide) (by decide) cover7634 (by decide)
  decide +kernel

theorem contract7634_1 : P.leaf 30 122147 = 21440 := by
  exact leaf_contract_factors (k := 30) (b := 20) (H := 122147) (ss := [(6, 1, 478), (12, 1, 478), (10, 1, 458), (2, 1, 487), (3, 1, 523), (30, 18, 867), (18, 1, 879), (14, 1, 965), (31, 1, 1251), (28, 1, 858)]) (ids := [2, 3, 5, 6, 7, 9, 11, 13, 14, 15, 17, 18, 19, 20, 23, 24, 25, 27, 21, 22]) (cs := [1, 1, 2, 3, 1, 4, 5, 6, 1, 7, 1, 8, 1, 9, 10, 11, 1, 12, 13, 14, 15, 20, 21, 16, 17, 18, 1, 19, 1, 1]) (bs := [18, 2]) (W := 21440) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c7634_1 : P.sumLeaves 24 7817408 64 = 21440 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 122147) rows (by decide) (by decide)).symm.trans contract7634_1

theorem c7634_2 : P.sumLeaves 24 7817472 512 = 352156 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7634) (lo := 256) (len := 512) (W := 352156) check rows elimOK (by decide) (by decide) cover7634 (by decide)
  decide +kernel

theorem contract7634_3 : P.leaf 30 122156 = 29216 := by
  exact leaf_contract_factors (k := 30) (b := 18) (H := 122156) (ss := [(2, 1, 466), (6, 1, 478), (12, 1, 478), (10, 1, 458), (5, 1, 523), (8, 1, 537), (17, 1, 537), (30, 1, 866), (26, 1, 516), (31, 1, 516), (28, 1, 858), (11, 1, 879)]) (ids := [1, 2, 5, 7, 11, 12, 13, 14, 16, 17, 18, 19, 20, 23, 25, 27, 21, 22]) (cs := [1, 2, 3, 1, 1, 4, 1, 5, 1, 1, 1, 6, 7, 8, 9, 1, 10, 11, 12, 13, 14, 18, 19, 15, 1, 16, 1, 17, 1, 1]) (bs := [16, 2]) (W := 29216) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c7634_3 : P.sumLeaves 24 7817984 64 = 29216 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 122156) rows (by decide) (by decide)).symm.trans contract7634_3

theorem contract7634_4 : P.leaf 30 122157 = 71632 := by
  exact leaf_contract_factors (k := 30) (b := 20) (H := 122157) (ss := [(6, 1, 478), (12, 1, 478), (10, 1, 458), (8, 1, 537), (17, 1, 537), (30, 1, 867), (26, 1, 516), (31, 1, 516), (28, 1, 858), (11, 1, 879)]) (ids := [0, 1, 2, 3, 5, 7, 11, 12, 13, 14, 16, 17, 18, 19, 20, 23, 25, 27, 21, 22]) (cs := [2, 3, 4, 5, 1, 6, 1, 7, 1, 1, 1, 8, 9, 10, 11, 1, 12, 13, 14, 15, 16, 20, 21, 17, 1, 18, 1, 19, 1, 1]) (bs := [18, 2]) (W := 71632) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c7634_4 : P.sumLeaves 24 7818048 64 = 71632 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 122157) rows (by decide) (by decide)).symm.trans contract7634_4

theorem c7634_5 : P.sumLeaves 24 7818112 128 = 580880 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7634) (lo := 896) (len := 128) (W := 580880) check rows elimOK (by decide) (by decide) cover7634 (by decide)
  decide +kernel

theorem h7634 : P.leaf 34 7634 = 1062300 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(192, 6976), (64, 21440), (512, 352156), (64, 29216), (64, 71632), (128, 580880)]) (.cons c7634_0 (.cons c7634_1 (.cons c7634_2 (.cons c7634_3 (.cons c7634_4 (.cons c7634_5 (.nil))))))) (by decide) (by decide))

theorem cover7635 : P.CoversSplit 24 10 7635 0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ccfc000000000000cc00000000000000ccfc000000000000cc00000000000000ffff000000000000ffff00000000000000000000000000000000000000000000ccfc000000000000cc0000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 858, 865, 866, 867, 916, 1202, 1209, 1210, 1251, 1601, 1609]) (ps := [(8, [1272], [1266])]) (by decide +kernel)

theorem c7635_0 : P.sumLeaves 24 7818240 128 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7635) (lo := 0) (len := 128) (W := 0) check rows elimOK (by decide) (by decide) cover7635 (by decide)
  decide +kernel

theorem contract7635_1 : P.leaf 30 122162 = 43104 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 122162) (ss := [(2, 1, 487), (5, 1, 523), (3, 1, 536), (30, 1, 866), (12, 1, 916), (29, 1, 916), (14, 1, 965), (18, 1, 965), (13, 1, 922), (31, 1, 1251), (27, 1, 1601)]) (ids := [2, 4, 5, 6, 7, 8, 9, 13, 14, 15, 17, 18, 19, 20, 21, 22, 24, 26, 23]) (cs := [1, 1, 2, 1, 3, 4, 5, 6, 7, 8, 1, 1, 1, 9, 10, 11, 1, 12, 13, 14, 15, 16, 17, 20, 18, 1, 19, 1, 1, 1]) (bs := [18, 1]) (W := 43104) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c7635_1 : P.sumLeaves 24 7818368 64 = 43104 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 122162) rows (by decide) (by decide)).symm.trans contract7635_1

theorem c7635_2 : P.sumLeaves 24 7818432 698 = 5955981 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7635) (lo := 192) (len := 698) (W := 5955981) check rows elimOK (by decide) (by decide) cover7635 (by decide)
  decide +kernel

theorem c7635_3 : P.sumLeaves 24 7819130 134 = 8667292 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7635) (lo := 890) (len := 134) (W := 8667292) check rows elimOK (by decide) (by decide) cover7635 (by decide)
  decide +kernel

theorem h7635 : P.leaf 34 7635 = 14666377 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(128, 0), (64, 43104), (698, 5955981), (134, 8667292)]) (.cons c7635_0 (.cons c7635_1 (.cons c7635_2 (.cons c7635_3 (.nil))))) (by decide) (by decide))

theorem cover7636 : P.CoversSplit 24 10 7636 0xf0000000000000000000000000000000a0000000000000000000000000000000c000000000000000c00000000000000080000000000000008000000000000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 516, 858, 865, 866, 916, 1202, 1210, 1251, 1259, 1601]) (ps := [(8, [1272], [1266])]) (by decide +kernel)

theorem c7636_0 : P.sumLeaves 24 7819264 1024 = 685728 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7636) (lo := 0) (len := 1024) (W := 685728) check rows elimOK (by decide) (by decide) cover7636 (by decide)
  decide +kernel

theorem h7636 : P.leaf 34 7636 = 685728 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 685728)]) (.cons c7636_0 (.nil)) (by decide) (by decide))

theorem cover7637 : P.CoversSplit 24 10 7637 0xff000000000000000000000000000000ff000000000000000000000000000000cc030000000000000000000000000000cc030000000000000000000000000000ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 516, 858, 865, 866, 916, 1202, 1209, 1210, 1251, 1601]) (ps := [(8, [1272], [1266])]) (by decide +kernel)

theorem c7637_0 : P.sumLeaves 24 7820288 1024 = 6470872 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7637) (lo := 0) (len := 1024) (W := 6470872) check rows elimOK (by decide) (by decide) cover7637 (by decide)
  decide +kernel

theorem h7637 : P.leaf 34 7637 = 6470872 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6470872)]) (.cons c7637_0 (.nil)) (by decide) (by decide))

theorem cover7638 : P.CoversSplit 24 10 7638 0xf0f0000000000000f0f0000000000000a0a0000000000000a0a0000000000000c0f0000000000000c00000000000000080a00000000000008000000000000000f0f0000000000000f0f000000000000000000000000000000000000000000000c0f0000000000000c00000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 516, 858, 865, 866, 1210, 1251, 1601, 1609]) (ps := [(8, [1272], [1266])]) (by decide +kernel)

theorem c7638_0 : P.sumLeaves 24 7821312 1024 = 11715344 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7638) (lo := 0) (len := 1024) (W := 11715344) check rows elimOK (by decide) (by decide) cover7638 (by decide)
  decide +kernel

theorem h7638 : P.leaf 34 7638 = 11715344 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 11715344)]) (.cons c7638_0 (.nil)) (by decide) (by decide))

theorem cover7639 : P.CoversSplit 24 10 7639 0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ccfc000000000000cc00000000000000ccfc000000000000cc00000000000000ffff000000000000ffff00000000000000000000000000000000000000000000ccfc000000000000cc0000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 858, 865, 866, 1202, 1209, 1210, 1251, 1259, 1601, 1609]) (ps := [(8, [1272], [1266])]) (by decide +kernel)

theorem c7639_0 : P.sumLeaves 24 7822336 886 = 19230196 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7639) (lo := 0) (len := 886) (W := 19230196) check rows elimOK (by decide) (by decide) cover7639 (by decide)
  decide +kernel

theorem c7639_1 : P.sumLeaves 24 7823222 138 = 29187250 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7639) (lo := 886) (len := 138) (W := 29187250) check rows elimOK (by decide) (by decide) cover7639 (by decide)
  decide +kernel

theorem h7639 : P.leaf 34 7639 = 48417446 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(886, 19230196), (138, 29187250)]) (.cons c7639_0 (.cons c7639_1 (.nil))) (by decide) (by decide))

theorem cover7640 : P.CoversSplit 24 10 7640 0xf0000000000000000000000000000000a0000000000000000000000000000000c000000000000000c00000000000000080000000000000008000000000000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000c00000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 516, 858, 865, 867, 909, 916, 1202, 1210, 1251, 1259, 1601]) (ps := [(8, [1272], [1266])]) (by decide +kernel)

theorem c7640_0 : P.sumLeaves 24 7823360 1024 = 799912 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7640) (lo := 0) (len := 1024) (W := 799912) check rows elimOK (by decide) (by decide) cover7640 (by decide)
  decide +kernel

theorem h7640 : P.leaf 34 7640 = 799912 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 799912)]) (.cons c7640_0 (.nil)) (by decide) (by decide))

theorem cover7641 : P.CoversSplit 24 10 7641 0xff000000000000000000000000000000ff000000000000000000000000000000cc030000000000000000000000000000cc030000000000000000000000000000ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 516, 858, 865, 867, 916, 1202, 1209, 1210, 1251, 1601]) (ps := [(8, [1272], [1266])]) (by decide +kernel)

theorem c7641_0 : P.sumLeaves 24 7824384 1024 = 4548004 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7641) (lo := 0) (len := 1024) (W := 4548004) check rows elimOK (by decide) (by decide) cover7641 (by decide)
  decide +kernel

theorem h7641 : P.leaf 34 7641 = 4548004 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4548004)]) (.cons c7641_0 (.nil)) (by decide) (by decide))

theorem cover7642 : P.CoversSplit 24 10 7642 0xf0f0000000000000f0f0000000000000a0a0000000000000a0a0000000000000c0f0000000000000c00000000000000080a00000000000008000000000000000f0f0000000000000f0f000000000000000000000000000000000000000000000c0f0000000000000c00000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 516, 858, 865, 867, 909, 1210, 1251, 1601, 1609]) (ps := [(8, [1272], [1266])]) (by decide +kernel)

theorem c7642_0 : P.sumLeaves 24 7825408 1024 = 4389888 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7642) (lo := 0) (len := 1024) (W := 4389888) check rows elimOK (by decide) (by decide) cover7642 (by decide)
  decide +kernel

theorem h7642 : P.leaf 34 7642 = 4389888 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4389888)]) (.cons c7642_0 (.nil)) (by decide) (by decide))

theorem cover7643 : P.CoversSplit 24 10 7643 0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ccfc000000000000cc00000000000000ccfc000000000000cc00000000000000ffff000000000000ffff00000000000000000000000000000000000000000000ccfc000000000000cc0000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 858, 865, 867, 916, 1202, 1209, 1210, 1251, 1601, 1609]) (ps := [(8, [1272], [1266])]) (by decide +kernel)

theorem c7643_0 : P.sumLeaves 24 7826432 886 = 9340260 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7643) (lo := 0) (len := 886) (W := 9340260) check rows elimOK (by decide) (by decide) cover7643 (by decide)
  decide +kernel

theorem c7643_1 : P.sumLeaves 24 7827318 138 = 12781352 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7643) (lo := 886) (len := 138) (W := 12781352) check rows elimOK (by decide) (by decide) cover7643 (by decide)
  decide +kernel

theorem h7643 : P.leaf 34 7643 = 22121612 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(886, 9340260), (138, 12781352)]) (.cons c7643_0 (.cons c7643_1 (.nil))) (by decide) (by decide))

theorem cover7644 : P.CoversSplit 24 10 7644 0xf0000000000000000000000000000000a0000000000000000000000000000000c000000000000000c00000000000000080000000000000008000000000000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 516, 858, 865, 916, 1202, 1210, 1251, 1259, 1601]) (ps := [(8, [1272], [1266])]) (by decide +kernel)

theorem c7644_0 : P.sumLeaves 24 7827456 1024 = 2886732 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7644) (lo := 0) (len := 1024) (W := 2886732) check rows elimOK (by decide) (by decide) cover7644 (by decide)
  decide +kernel

theorem h7644 : P.leaf 34 7644 = 2886732 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2886732)]) (.cons c7644_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(7608, 48), (7609, 48), (7610, 48), (7611, 48), (7612, 48), (7613, 48), (7614, 48), (7615, 48), (7616, 12), (7617, 48), (7619, 24), (7620, 24), (7621, 48), (7623, 24), (7624, 24), (7625, 48), (7627, 24), (7628, 24), (7629, 48), (7631, 24), (7633, 24), (7634, 24), (7635, 48), (7636, 48), (7637, 48), (7638, 48), (7639, 48), (7640, 48), (7641, 48), (7642, 48), (7643, 48), (7644, 48)]

theorem segOK : checkSeg 16 perms 7608 7645 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 7608 7645 1284 12863095608 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 12863095608)
    (SegSum.cons (w := 48) h7608 (SegSum.cons (w := 48) h7609 (SegSum.cons (w := 48) h7610 (SegSum.cons (w := 48) h7611 (SegSum.cons (w := 48) h7612 (SegSum.cons (w := 48) h7613 (SegSum.cons (w := 48) h7614 (SegSum.cons (w := 48) h7615 (SegSum.cons (w := 12) h7616 (SegSum.cons (w := 48) h7617 (SegSum.cons (w := 24) h7619 (SegSum.cons (w := 24) h7620 (SegSum.cons (w := 48) h7621 (SegSum.cons (w := 24) h7623 (SegSum.cons (w := 24) h7624 (SegSum.cons (w := 48) h7625 (SegSum.cons (w := 24) h7627 (SegSum.cons (w := 24) h7628 (SegSum.cons (w := 48) h7629 (SegSum.cons (w := 24) h7631 (SegSum.cons (w := 24) h7633 (SegSum.cons (w := 24) h7634 (SegSum.cons (w := 48) h7635 (SegSum.cons (w := 48) h7636 (SegSum.cons (w := 48) h7637 (SegSum.cons (w := 48) h7638 (SegSum.cons (w := 48) h7639 (SegSum.cons (w := 48) h7640 (SegSum.cons (w := 48) h7641 (SegSum.cons (w := 48) h7642 (SegSum.cons (w := 48) h7643 (SegSum.cons (w := 48) h7644 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S51
