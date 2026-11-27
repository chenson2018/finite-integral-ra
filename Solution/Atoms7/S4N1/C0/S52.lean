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

namespace RACert.S4N1.C0.S52

open RACert RACert.Problem

theorem cover7645 : P.CoversSplit 24 10 7645 0xff000000000000000000000000000000ff000000000000000000000000000000cc030000000000000000000000000000cc030000000000000000000000000000ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 516, 858, 865, 916, 1202, 1209, 1210, 1251, 1601]) (ps := [(8, [1272], [1266])]) (by decide +kernel)

theorem c7645_0 : P.sumLeaves 24 7828480 1024 = 17036670 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7645) (lo := 0) (len := 1024) (W := 17036670) check rows elimOK (by decide) (by decide) cover7645 (by decide)
  decide +kernel

theorem h7645 : P.leaf 34 7645 = 17036670 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 17036670)]) (.cons c7645_0 (.nil)) (by decide) (by decide))

theorem cover7646 : P.CoversSplit 24 10 7646 0xf0f0000000000000f0f0000000000000a0a0000000000000a0a0000000000000c0f0000000000000c00000000000000080a00000000000008000000000000000f0f0000000000000f0f000000000000000000000000000000000000000000000c0f0000000000000c00000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 516, 858, 865, 1210, 1251, 1601, 1609]) (ps := [(8, [1272], [1266])]) (by decide +kernel)

theorem c7646_0 : P.sumLeaves 24 7829504 1024 = 20997958 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7646) (lo := 0) (len := 1024) (W := 20997958) check rows elimOK (by decide) (by decide) cover7646 (by decide)
  decide +kernel

theorem h7646 : P.leaf 34 7646 = 20997958 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 20997958)]) (.cons c7646_0 (.nil)) (by decide) (by decide))

theorem cover7647 : P.CoversSplit 24 10 7647 0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ccfc000000000000cc00000000000000ccfc000000000000cc00000000000000ffff000000000000ffff00000000000000000000000000000000000000000000ccfc000000000000cc0000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 858, 865, 1202, 1209, 1210, 1251, 1259, 1601, 1609]) (ps := [(8, [1272], [1266])]) (by decide +kernel)

theorem c7647_0 : P.sumLeaves 24 7830528 886 = 34355743 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7647) (lo := 0) (len := 886) (W := 34355743) check rows elimOK (by decide) (by decide) cover7647 (by decide)
  decide +kernel

theorem c7647_1 : P.sumLeaves 24 7831414 138 = 41860310 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7647) (lo := 886) (len := 138) (W := 41860310) check rows elimOK (by decide) (by decide) cover7647 (by decide)
  decide +kernel

theorem h7647 : P.leaf 34 7647 = 76216053 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(886, 34355743), (138, 41860310)]) (.cons c7647_0 (.cons c7647_1 (.nil))) (by decide) (by decide))

theorem cover7648 : P.CoversSplit 24 10 7648 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c7648_0 : P.sumLeaves 24 7831552 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7648) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7648 (by decide)
  decide +kernel

theorem h7648 : P.leaf 34 7648 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7648_0 (.nil)) (by decide) (by decide))

theorem cover7649 : P.CoversSplit 24 10 7649 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 858, 865, 916, 1209, 1258, 1266]) (by decide +kernel)

theorem c7649_0 : P.sumLeaves 24 7832576 1024 = 274472 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7649) (lo := 0) (len := 1024) (W := 274472) check rows elimOK (by decide) (by decide) cover7649 (by decide)
  decide +kernel

theorem h7649 : P.leaf 34 7649 = 274472 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 274472)]) (.cons c7649_0 (.nil)) (by decide) (by decide))

theorem cover7650 : P.CoversSplit 24 10 7650 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 522, 858, 865, 1209, 1217, 1258, 1266]) (by decide +kernel)

theorem c7650_0 : P.sumLeaves 24 7833600 1024 = 159616 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7650) (lo := 0) (len := 1024) (W := 159616) check rows elimOK (by decide) (by decide) cover7650 (by decide)
  decide +kernel

theorem h7650 : P.leaf 34 7650 = 159616 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 159616)]) (.cons c7650_0 (.nil)) (by decide) (by decide))

theorem cover7651 : P.CoversSplit 24 10 7651 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 858, 865, 867, 916, 1209, 1217, 1258, 1266]) (by decide +kernel)

theorem c7651_0 : P.sumLeaves 24 7834624 1024 = 1987024 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7651) (lo := 0) (len := 1024) (W := 1987024) check rows elimOK (by decide) (by decide) cover7651 (by decide)
  decide +kernel

theorem h7651 : P.leaf 34 7651 = 1987024 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1987024)]) (.cons c7651_0 (.nil)) (by decide) (by decide))

theorem cover7652 : P.CoversSplit 24 10 7652 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c7652_0 : P.sumLeaves 24 7835648 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7652) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7652 (by decide)
  decide +kernel

theorem h7652 : P.leaf 34 7652 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7652_0 (.nil)) (by decide) (by decide))

theorem cover7653 : P.CoversSplit 24 10 7653 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 858, 865, 916, 1209, 1258, 1266]) (by decide +kernel)

theorem c7653_0 : P.sumLeaves 24 7836672 1024 = 871068 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7653) (lo := 0) (len := 1024) (W := 871068) check rows elimOK (by decide) (by decide) cover7653 (by decide)
  decide +kernel

theorem h7653 : P.leaf 34 7653 = 871068 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 871068)]) (.cons c7653_0 (.nil)) (by decide) (by decide))

theorem cover7654 : P.CoversSplit 24 10 7654 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 522, 858, 865, 1209, 1217, 1258, 1266]) (by decide +kernel)

theorem c7654_0 : P.sumLeaves 24 7837696 1024 = 2830112 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7654) (lo := 0) (len := 1024) (W := 2830112) check rows elimOK (by decide) (by decide) cover7654 (by decide)
  decide +kernel

theorem h7654 : P.leaf 34 7654 = 2830112 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2830112)]) (.cons c7654_0 (.nil)) (by decide) (by decide))

theorem cover7655 : P.CoversSplit 24 10 7655 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 858, 865, 867, 916, 1209, 1217, 1258, 1266]) (by decide +kernel)

theorem c7655_0 : P.sumLeaves 24 7838720 1024 = 5027810 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7655) (lo := 0) (len := 1024) (W := 5027810) check rows elimOK (by decide) (by decide) cover7655 (by decide)
  decide +kernel

theorem h7655 : P.leaf 34 7655 = 5027810 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5027810)]) (.cons c7655_0 (.nil)) (by decide) (by decide))

theorem cover7656 : P.CoversSplit 24 10 7656 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c7656_0 : P.sumLeaves 24 7839744 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7656) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7656 (by decide)
  decide +kernel

theorem h7656 : P.leaf 34 7656 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7656_0 (.nil)) (by decide) (by decide))

theorem cover7657 : P.CoversSplit 24 10 7657 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 858, 865, 916, 1209, 1258, 1266]) (by decide +kernel)

theorem c7657_0 : P.sumLeaves 24 7840768 1024 = 1069992 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7657) (lo := 0) (len := 1024) (W := 1069992) check rows elimOK (by decide) (by decide) cover7657 (by decide)
  decide +kernel

theorem h7657 : P.leaf 34 7657 = 1069992 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1069992)]) (.cons c7657_0 (.nil)) (by decide) (by decide))

theorem cover7658 : P.CoversSplit 24 10 7658 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 522, 858, 865, 1209, 1217, 1258, 1266]) (by decide +kernel)

theorem c7658_0 : P.sumLeaves 24 7841792 1024 = 1232828 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7658) (lo := 0) (len := 1024) (W := 1232828) check rows elimOK (by decide) (by decide) cover7658 (by decide)
  decide +kernel

theorem h7658 : P.leaf 34 7658 = 1232828 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1232828)]) (.cons c7658_0 (.nil)) (by decide) (by decide))

theorem cover7659 : P.CoversSplit 24 10 7659 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 858, 865, 867, 916, 1209, 1217, 1258, 1266]) (by decide +kernel)

theorem c7659_0 : P.sumLeaves 24 7842816 1024 = 2122130 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7659) (lo := 0) (len := 1024) (W := 2122130) check rows elimOK (by decide) (by decide) cover7659 (by decide)
  decide +kernel

theorem h7659 : P.leaf 34 7659 = 2122130 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2122130)]) (.cons c7659_0 (.nil)) (by decide) (by decide))

theorem cover7660 : P.CoversSplit 24 10 7660 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c7660_0 : P.sumLeaves 24 7843840 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7660) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7660 (by decide)
  decide +kernel

theorem h7660 : P.leaf 34 7660 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7660_0 (.nil)) (by decide) (by decide))

theorem cover7661 : P.CoversSplit 24 10 7661 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 858, 865, 916, 1209, 1258, 1266]) (by decide +kernel)

theorem c7661_0 : P.sumLeaves 24 7844864 1024 = 2088228 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7661) (lo := 0) (len := 1024) (W := 2088228) check rows elimOK (by decide) (by decide) cover7661 (by decide)
  decide +kernel

theorem h7661 : P.leaf 34 7661 = 2088228 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2088228)]) (.cons c7661_0 (.nil)) (by decide) (by decide))

theorem cover7662 : P.CoversSplit 24 10 7662 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 522, 858, 865, 1209, 1217, 1258, 1266]) (by decide +kernel)

theorem c7662_0 : P.sumLeaves 24 7845888 1024 = 3697640 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7662) (lo := 0) (len := 1024) (W := 3697640) check rows elimOK (by decide) (by decide) cover7662 (by decide)
  decide +kernel

theorem h7662 : P.leaf 34 7662 = 3697640 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3697640)]) (.cons c7662_0 (.nil)) (by decide) (by decide))

theorem cover7663 : P.CoversSplit 24 10 7663 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 858, 865, 867, 916, 1209, 1217, 1258, 1266]) (by decide +kernel)

theorem c7663_0 : P.sumLeaves 24 7846912 1024 = 5594693 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7663) (lo := 0) (len := 1024) (W := 5594693) check rows elimOK (by decide) (by decide) cover7663 (by decide)
  decide +kernel

theorem h7663 : P.leaf 34 7663 = 5594693 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5594693)]) (.cons c7663_0 (.nil)) (by decide) (by decide))

theorem cover7665 : P.CoversSplit 24 10 7665 0xff000000ff0000000000000000000000ff000000ff0000000000000000000000cc030000880000000000000000000000cc030000880000000000000000000000ff000000ff0000000000000000000000ff000000fa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 858, 865, 866, 867, 916, 1209, 1210, 1217, 1601]) (by decide +kernel)

theorem c7665_0 : P.sumLeaves 24 7848960 1024 = 5905713 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7665) (lo := 0) (len := 1024) (W := 5905713) check rows elimOK (by decide) (by decide) cover7665 (by decide)
  decide +kernel

theorem h7665 : P.leaf 34 7665 = 5905713 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5905713)]) (.cons c7665_0 (.nil)) (by decide) (by decide))

theorem cover7666 : P.CoversSplit 24 10 7666 0xf0f00000f0f50000f0f00000f0f50000f0f00000f0f50000f0f00000f0f50000c0f0000080800000c000000080000000c0f0000080800000c000000080000000f0f00000f0f50000f0f00000f0f50000f0f00000f0f00000f0f00000f0f00000c0f0000080800000c000000080000000c0c0000080800000c000000080000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 858, 865, 866, 867, 908, 909, 1210, 1217, 1258, 1601, 1609]) (by decide +kernel)

theorem c7666_0 : P.sumLeaves 24 7849984 631 = 2222300 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7666) (lo := 0) (len := 631) (W := 2222300) check rows elimOK (by decide) (by decide) cover7666 (by decide)
  decide +kernel

theorem c7666_1 : P.sumLeaves 24 7850615 393 = 6016658 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7666) (lo := 631) (len := 393) (W := 6016658) check rows elimOK (by decide) (by decide) cover7666 (by decide)
  decide +kernel

theorem h7666 : P.leaf 34 7666 = 8238958 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(631, 2222300), (393, 6016658)]) (.cons c7666_0 (.cons c7666_1 (.nil))) (by decide) (by decide))

theorem cover7667 : P.CoversSplit 24 10 7667 0xffff0000fffa0000ffff0000fffa0000ffff0000fffa0000ffff0000fffa0000ccfc000088880000cc00000088000000ccfc000088880000cc00000088000000ffff0000fffa0000ffff0000fffa0000ffff0000fafa0000ffff0000fafa0000ccfc000088880000cc00000088000000cccc000088880000cc00000088000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [858, 865, 866, 867, 916, 1209, 1210, 1217, 1258, 1601, 1609]) (by decide +kernel)

theorem c7667_0 : P.sumLeaves 24 7851008 404 = 4957276 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7667) (lo := 0) (len := 404) (W := 4957276) check rows elimOK (by decide) (by decide) cover7667 (by decide)
  decide +kernel

theorem c7667_1 : P.sumLeaves 24 7851412 362 = 13978004 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7667) (lo := 404) (len := 362) (W := 13978004) check rows elimOK (by decide) (by decide) cover7667 (by decide)
  decide +kernel

theorem c7667_2 : P.sumLeaves 24 7851774 216 = 23518246 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7667) (lo := 766) (len := 216) (W := 23518246) check rows elimOK (by decide) (by decide) cover7667 (by decide)
  decide +kernel

theorem c7667_3 : P.sumLeaves 24 7851990 42 = 17767474 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7667) (lo := 982) (len := 42) (W := 17767474) check rows elimOK (by decide) (by decide) cover7667 (by decide)
  decide +kernel

theorem h7667 : P.leaf 34 7667 = 60221000 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(404, 4957276), (362, 13978004), (216, 23518246), (42, 17767474)]) (.cons c7667_0 (.cons c7667_1 (.cons c7667_2 (.cons c7667_3 (.nil))))) (by decide) (by decide))

theorem cover7668 : P.CoversSplit 24 10 7668 0xf0000000f000aa000000000000000000f0000000f0000a000000000000000000c000000080088808c0c0000080880000c000000080080808c0c0000080880000f0000000f000aa000000000000000000f0000000f0000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 858, 865, 866, 916, 1210, 1601]) (ps := [(11, [879, 909], [858])]) (by decide +kernel)

theorem c7668_0 : P.sumLeaves 24 7852032 1024 = 3803616 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7668) (lo := 0) (len := 1024) (W := 3803616) check rows elimOK (by decide) (by decide) cover7668 (by decide)
  decide +kernel

theorem h7668 : P.leaf 34 7668 = 3803616 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3803616)]) (.cons c7668_0 (.nil)) (by decide) (by decide))

theorem cover7669 : P.CoversSplit 24 10 7669 0xff00ff00ff00a0000000000000000000ff00ff00ff00a0000000000000000000cc03cc03880080000000000000000000cc03cc03880080000000000000000000ff00ff00ff00a0000000000000000000ff00ff00fa00a00000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 858, 865, 866, 916, 1209, 1210, 1217, 1601]) (by decide +kernel)

theorem c7669_0 : P.sumLeaves 24 7853056 878 = 8468356 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7669) (lo := 0) (len := 878) (W := 8468356) check rows elimOK (by decide) (by decide) cover7669 (by decide)
  decide +kernel

theorem c7669_1 : P.sumLeaves 24 7853934 146 = 11847388 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7669) (lo := 878) (len := 146) (W := 11847388) check rows elimOK (by decide) (by decide) cover7669 (by decide)
  decide +kernel

theorem h7669 : P.leaf 34 7669 = 20315744 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(878, 8468356), (146, 11847388)]) (.cons c7669_0 (.cons c7669_1 (.nil))) (by decide) (by decide))

theorem cover7670 : P.CoversSplit 24 10 7670 0xf0f00000f0f50000f0f00000f0f50000f0f00000f0f50000f0f00000f0f50000c0f0000080800000c000000080000000c0f0000080800000c000000080000000f0f00000f0f50000f0f00000f0f50000f0f00000f0f00000f0f00000f0f00000c0f0000080800000c000000080000000c0c0000080800000c000000080000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 858, 865, 866, 908, 1210, 1217, 1258, 1601, 1609]) (by decide +kernel)

theorem c7670_0 : P.sumLeaves 24 7854080 631 = 12518611 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7670) (lo := 0) (len := 631) (W := 12518611) check rows elimOK (by decide) (by decide) cover7670 (by decide)
  decide +kernel

theorem c7670_1 : P.sumLeaves 24 7854711 393 = 45712807 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7670) (lo := 631) (len := 393) (W := 45712807) check rows elimOK (by decide) (by decide) cover7670 (by decide)
  decide +kernel

theorem h7670 : P.leaf 34 7670 = 58231418 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(631, 12518611), (393, 45712807)]) (.cons c7670_0 (.cons c7670_1 (.nil))) (by decide) (by decide))

theorem cover7671 : P.CoversSplit 24 10 7671 0xfffffffffffaaaaaffff0000fffa0000fffffffffffaaaaaffff0000fffa0000ccfcccfc88888888cccc000088880000ccfcccfc88888888cccc000088880000fffffffffffaaaaaffff0000fffa0000fffffffffafaaaaaffff0000fafa0000ccfcccfc88888888cccc000088880000cccccccc88888888cccc000088880000 :=
  coversSplit check rows (by decide) (by decide) (xs := [858, 865, 866, 1209, 1210, 1217, 1258, 1601, 1609]) (by decide +kernel)

theorem c7671_0 : P.sumLeaves 24 7855104 312 = 5032686 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7671) (lo := 0) (len := 312) (W := 5032686) check rows elimOK (by decide) (by decide) cover7671 (by decide)
  decide +kernel

theorem c7671_1 : P.sumLeaves 24 7855416 149 = 23989817 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7671) (lo := 312) (len := 149) (W := 23989817) check rows elimOK (by decide) (by decide) cover7671 (by decide)
  decide +kernel

theorem c7671_2 : P.sumLeaves 24 7855565 237 = 40317103 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7671) (lo := 461) (len := 237) (W := 40317103) check rows elimOK (by decide) (by decide) cover7671 (by decide)
  decide +kernel

theorem c7671_3 : P.sumLeaves 24 7855802 178 = 40333393 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7671) (lo := 698) (len := 178) (W := 40333393) check rows elimOK (by decide) (by decide) cover7671 (by decide)
  decide +kernel

theorem c7671_4 : P.sumLeaves 24 7855980 140 = 92141602 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7671) (lo := 876) (len := 140) (W := 92141602) check rows elimOK (by decide) (by decide) cover7671 (by decide)
  decide +kernel

theorem c7671_5 : P.sumLeaves 24 7856120 8 = 23819128 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7671) (lo := 1016) (len := 8) (W := 23819128) check rows elimOK (by decide) (by decide) cover7671 (by decide)
  decide +kernel

theorem h7671 : P.leaf 34 7671 = 225633729 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(312, 5032686), (149, 23989817), (237, 40317103), (178, 40333393), (140, 92141602), (8, 23819128)]) (.cons c7671_0 (.cons c7671_1 (.cons c7671_2 (.cons c7671_3 (.cons c7671_4 (.cons c7671_5 (.nil))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(7645, 48), (7646, 48), (7647, 48), (7648, 24), (7649, 48), (7650, 48), (7651, 48), (7652, 48), (7653, 48), (7654, 48), (7655, 48), (7656, 48), (7657, 48), (7658, 48), (7659, 48), (7660, 48), (7661, 48), (7662, 48), (7663, 48), (7665, 24), (7666, 48), (7667, 48), (7668, 48), (7669, 48), (7670, 48), (7671, 48)]

theorem segOK : checkSeg 16 perms 7645 7672 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 7645 7672 1200 24988973544 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 24988973544)
    (SegSum.cons (w := 48) h7645 (SegSum.cons (w := 48) h7646 (SegSum.cons (w := 48) h7647 (SegSum.cons (w := 24) h7648 (SegSum.cons (w := 48) h7649 (SegSum.cons (w := 48) h7650 (SegSum.cons (w := 48) h7651 (SegSum.cons (w := 48) h7652 (SegSum.cons (w := 48) h7653 (SegSum.cons (w := 48) h7654 (SegSum.cons (w := 48) h7655 (SegSum.cons (w := 48) h7656 (SegSum.cons (w := 48) h7657 (SegSum.cons (w := 48) h7658 (SegSum.cons (w := 48) h7659 (SegSum.cons (w := 48) h7660 (SegSum.cons (w := 48) h7661 (SegSum.cons (w := 48) h7662 (SegSum.cons (w := 48) h7663 (SegSum.cons (w := 24) h7665 (SegSum.cons (w := 48) h7666 (SegSum.cons (w := 48) h7667 (SegSum.cons (w := 48) h7668 (SegSum.cons (w := 48) h7669 (SegSum.cons (w := 48) h7670 (SegSum.cons (w := 48) h7671 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S52
