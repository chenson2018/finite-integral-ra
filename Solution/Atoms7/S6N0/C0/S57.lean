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

namespace RACert.S6N0.C0.S57

open RACert RACert.Problem

theorem cover88703 : P.CoversSplit 26 10 88703 0xfffffffffffcfaf800000000000000000000000000000000000000000f0c0a080f0f0a0a0f0c0a080a0a0a0a0a080a080000000000000000000000000a080a0800000000ffccfac8000000000000000000000000ccccc8c8000000000c0c0808000000000f0c0a08000000000a080a08000000000c0c08080000000008080808 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 587, 922, 979, 1273, 1315, 1658, 1665]) (by decide +kernel)

noncomputable def f88703 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (90831872 + i)

theorem c88703_0 : rowSum f88703 0 1024 = 14215296 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 88703) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover88703 (by decide)
  decide +kernel

theorem sum88703 : rowSum f88703 0 1024 = 14215296 :=
  c88703_0

theorem h88703 : P.leaf 36 88703 = 14215296 :=
  leaf_weighted (k := 26) (d := 10) (H := 88703) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 88703) (by decide) (by decide +kernel)) sum88703

theorem cover88770 : P.CoversSplit 26 10 88770 0x8000000080000000c0000000c000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000300001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 524, 530, 587, 874, 922, 972, 979, 1266, 1315, 1665]) (by decide +kernel)

theorem c88770_0 : P.sumLeaves 26 90900480 1024 = 2401 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88770) (lo := 0) (len := 1024) (W := 2401) check rows elimOK (by decide) (by decide) cover88770 (by decide)
  decide +kernel

theorem h88770 : P.leaf 36 88770 = 2401 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2401)]) (.cons c88770_0 (.nil)) (by decide) (by decide))

theorem cover88771 : P.CoversSplit 26 10 88771 0x8000000080000000800000008000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000200001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 530, 587, 972, 979, 1266, 1273, 1315, 1665]) (by decide +kernel)

theorem c88771_0 : P.sumLeaves 26 90901504 1024 = 98125 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88771) (lo := 0) (len := 1024) (W := 98125) check rows elimOK (by decide) (by decide) cover88771 (by decide)
  decide +kernel

theorem h88771 : P.leaf 36 88771 = 98125 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 98125)]) (.cons c88771_0 (.nil)) (by decide) (by decide))

theorem cover88775 : P.CoversSplit 26 10 88775 0xcc000000cc000400cc000000cc00040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003300010000000000330000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 587, 922, 972, 979, 1266, 1315]) (by decide +kernel)

theorem c88775_0 : P.sumLeaves 26 90905600 1024 = 1334330 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88775) (lo := 0) (len := 1024) (W := 1334330) check rows elimOK (by decide) (by decide) cover88775 (by decide)
  decide +kernel

theorem h88775 : P.leaf 36 88775 = 1334330 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1334330)]) (.cons c88775_0 (.nil)) (by decide) (by decide))

theorem cover88778 : P.CoversSplit 26 10 88778 0xa0a00000a0a00000a0a00000a0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 524, 530, 874, 922, 972, 979, 1315, 1665]) (by decide +kernel)

theorem c88778_0 : P.sumLeaves 26 90908672 896 = 688 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88778) (lo := 0) (len := 896) (W := 688) check rows elimOK (by decide) (by decide) cover88778 (by decide)
  decide +kernel

theorem contract88778_1 : P.leaf 32 1420462 = 21120 := by
  exact leaf_contract_factors (k := 32) (b := 17) (H := 1420462) (ss := [(19, 1, 466), (8, 1, 479), (28, 1, 481), (30, 1, 481), (14, 1, 866), (16, 1, 515), (17, 1, 516), (15, 1, 865), (12, 1, 929), (7, 1, 460), (11, 1, 817), (18, 1, 1210), (21, 1, 1259), (32, 1, 1315), (20, 1, 1609)]) (ids := [0, 1, 2, 3, 4, 7, 8, 11, 20, 25, 27, 29, 31, 21, 22, 23, 24]) (cs := [2, 3, 4, 5, 6, 1, 1, 7, 8, 1, 1, 9, 1, 1, 1, 1, 1, 1, 1, 1, 10, 15, 16, 17, 18, 11, 1, 12, 1, 13, 1, 14]) (bs := [13, 4]) (W := 21120) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c88778_1 : P.sumLeaves 26 90909568 64 = 21120 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1420462) rows (by decide) (by decide)).symm.trans contract88778_1

theorem c88778_2 : P.sumLeaves 26 90909632 64 = 35060 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88778) (lo := 960) (len := 64) (W := 35060) check rows elimOK (by decide) (by decide) cover88778 (by decide)
  decide +kernel

theorem h88778 : P.leaf 36 88778 = 56868 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(896, 688), (64, 21120), (64, 35060)]) (.cons c88778_0 (.cons c88778_1 (.cons c88778_2 (.nil)))) (by decide) (by decide))

theorem cover88779 : P.CoversSplit 26 10 88779 0xa0a00000a0a00000a0a00000a0a0000000000000000000000000000020200000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 587, 972, 979, 1266, 1273, 1315, 1665]) (by decide +kernel)

theorem c88779_0 : P.sumLeaves 26 90909696 1024 = 678592 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88779) (lo := 0) (len := 1024) (W := 678592) check rows elimOK (by decide) (by decide) cover88779 (by decide)
  decide +kernel

theorem h88779 : P.leaf 36 88779 = 678592 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 678592)]) (.cons c88779_0 (.nil)) (by decide) (by decide))

theorem cover88782 : P.CoversSplit 26 10 88782 0xffff0000fffc0504ffff0000fffc050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000330001000000000033000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [524, 530, 874, 922, 972, 979, 1266, 1315, 1665]) (by decide +kernel)

theorem c88782_0 : P.sumLeaves 26 90912768 1024 = 614326 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88782) (lo := 0) (len := 1024) (W := 614326) check rows elimOK (by decide) (by decide) cover88782 (by decide)
  decide +kernel

theorem h88782 : P.leaf 36 88782 = 614326 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 614326)]) (.cons c88782_0 (.nil)) (by decide) (by decide))

theorem cover88783 : P.CoversSplit 26 10 88783 0xffff0000fffc0504ffff0000fffc050000000000000000000000000030300000000000000000000000000000000000000000000000000000000000000000000000000000330001000000000033000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 587, 922, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c88783_0 : P.sumLeaves 26 90913792 1024 = 5398116 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88783) (lo := 0) (len := 1024) (W := 5398116) check rows elimOK (by decide) (by decide) cover88783 (by decide)
  decide +kernel

theorem h88783 : P.leaf 36 88783 = 5398116 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5398116)]) (.cons c88783_0 (.nil)) (by decide) (by decide))

theorem cover88788 : P.CoversSplit 26 10 88788 0xcc000000cc000400cc000000cc00040000000000000000000000000000000000040004000400040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 559, 587, 874, 922, 923, 972, 979, 1315]) (by decide +kernel)

theorem c88788_0 : P.sumLeaves 26 90918912 704 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88788) (lo := 0) (len := 704) (W := 0) check rows elimOK (by decide) (by decide) cover88788 (by decide)
  decide +kernel

theorem contract88788_1 : P.leaf 32 1420619 = 4192 := by
  exact leaf_contract_factors (k := 32) (b := 16) (H := 1420619) (ss := [(29, 7, 475), (2, 1, 482), (7, 1, 487), (4, 1, 580), (11, 1, 459), (12, 1, 817), (13, 1, 461), (31, 1, 979), (28, 0, 1315), (30, 0, 1315), (26, 1, 481), (15, 1, 922), (9, 1, 473), (20, 1, 915), (21, 1, 573), (19, 1, 865)]) (ids := [1, 3, 4, 6, 8, 12, 14, 15, 16, 20, 22, 30, 31, 21, 23, 25]) (cs := [1, 2, 1, 3, 4, 1, 5, 1, 6, 1, 1, 1, 7, 1, 8, 9, 10, 1, 1, 1, 11, 15, 12, 16, 1, 17, 0, 1, 0, 1, 13, 14]) (bs := [13, 3]) (W := 4192) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c88788_1 : P.sumLeaves 26 90919616 64 = 4192 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1420619) rows (by decide) (by decide)).symm.trans contract88788_1

theorem c88788_2 : P.sumLeaves 26 90919680 256 = 155840 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88788) (lo := 768) (len := 256) (W := 155840) check rows elimOK (by decide) (by decide) cover88788 (by decide)
  decide +kernel

theorem h88788 : P.leaf 36 88788 = 160032 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(704, 0), (64, 4192), (256, 155840)]) (.cons c88788_0 (.cons c88788_1 (.cons c88788_2 (.nil)))) (by decide) (by decide))

theorem cover88789 : P.CoversSplit 26 10 88789 0xcc000000cc000400cc000000cc00040000000000000000000000000000000000040004000400040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 559, 587, 922, 923, 972, 979, 1315]) (by decide +kernel)

theorem c88789_0 : P.sumLeaves 26 90919936 704 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88789) (lo := 0) (len := 704) (W := 0) check rows elimOK (by decide) (by decide) cover88789 (by decide)
  decide +kernel

theorem contract88789_1 : P.leaf 32 1420635 = 20544 := by
  exact leaf_contract_factors (k := 32) (b := 18) (H := 1420635) (ss := [(29, 7, 475), (2, 1, 482), (7, 1, 487), (4, 1, 580), (11, 1, 459), (12, 1, 817), (31, 1, 979), (28, 0, 1315), (30, 0, 1315), (15, 1, 922), (9, 1, 473), (19, 1, 865), (21, 1, 573), (20, 1, 915)]) (ids := [1, 3, 4, 6, 8, 11, 12, 14, 15, 16, 20, 22, 24, 30, 31, 21, 23, 25]) (cs := [1, 2, 1, 3, 4, 1, 5, 1, 6, 1, 1, 7, 8, 1, 9, 10, 11, 1, 1, 1, 12, 17, 13, 18, 14, 19, 0, 1, 0, 1, 15, 16]) (bs := [15, 3]) (W := 20544) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c88789_1 : P.sumLeaves 26 90920640 64 = 20544 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1420635) rows (by decide) (by decide)).symm.trans contract88789_1

theorem c88789_2 : P.sumLeaves 26 90920704 256 = 1308920 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88789) (lo := 768) (len := 256) (W := 1308920) check rows elimOK (by decide) (by decide) cover88789 (by decide)
  decide +kernel

theorem h88789 : P.leaf 36 88789 = 1329464 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(704, 0), (64, 20544), (256, 1308920)]) (.cons c88789_0 (.cons c88789_1 (.cons c88789_2 (.nil)))) (by decide) (by decide))

theorem cover88790 : P.CoversSplit 26 10 88790 0xcc000000cc000400cc000000cc00040000000000000000000000000000000000040004000400040000000000000000000000000000000000000000000000000000000000003300010000000000330000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 587, 874, 922, 972, 979, 1315]) (by decide +kernel)

theorem c88790_0 : P.sumLeaves 26 90920960 1024 = 5540898 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88790) (lo := 0) (len := 1024) (W := 5540898) check rows elimOK (by decide) (by decide) cover88790 (by decide)
  decide +kernel

theorem h88790 : P.leaf 36 88790 = 5540898 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5540898)]) (.cons c88790_0 (.nil)) (by decide) (by decide))

theorem cover88791 : P.CoversSplit 26 10 88791 0xcc000000cc000400cc000000cc00040000000000000000000000000000000000040004000400040000000000000000000000000000000000000000000000000000000000003300010000000000330000000000000000000000000000000000000000000000010001000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 587, 922, 972, 979, 1315]) (by decide +kernel)

theorem c88791_0 : P.sumLeaves 26 90921984 1024 = 12044486 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88791) (lo := 0) (len := 1024) (W := 12044486) check rows elimOK (by decide) (by decide) cover88791 (by decide)
  decide +kernel

theorem h88791 : P.leaf 36 88791 = 12044486 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 12044486)]) (.cons c88791_0 (.nil)) (by decide) (by decide))

theorem cover88793 : P.CoversSplit 26 10 88793 0xa0a00000a0a00000a0a00000a0a0000000000000000000000000000020200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 587, 922, 923, 972, 1315, 1665]) (by decide +kernel)

theorem c88793_0 : P.sumLeaves 26 90924032 1024 = 1393400 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88793) (lo := 0) (len := 1024) (W := 1393400) check rows elimOK (by decide) (by decide) cover88793 (by decide)
  decide +kernel

theorem h88793 : P.leaf 36 88793 = 1393400 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1393400)]) (.cons c88793_0 (.nil)) (by decide) (by decide))

theorem cover88794 : P.CoversSplit 26 10 88794 0xa0a00000a0a00000a0a00000a0a0000000000000000000000000000020200000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 587, 874, 922, 972, 979, 1273, 1315, 1665]) (by decide +kernel)

theorem c88794_0 : P.sumLeaves 26 90925056 1024 = 1917528 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88794) (lo := 0) (len := 1024) (W := 1917528) check rows elimOK (by decide) (by decide) cover88794 (by decide)
  decide +kernel

theorem h88794 : P.leaf 36 88794 = 1917528 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1917528)]) (.cons c88794_0 (.nil)) (by decide) (by decide))

theorem cover88795 : P.CoversSplit 26 10 88795 0xa0a00000a0a00000a0a00000a0a0000000000000000000000000000020200000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 587, 972, 979, 1273, 1315, 1665]) (by decide +kernel)

theorem c88795_0 : P.sumLeaves 26 90926080 1024 = 9001884 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88795) (lo := 0) (len := 1024) (W := 9001884) check rows elimOK (by decide) (by decide) cover88795 (by decide)
  decide +kernel

theorem h88795 : P.leaf 36 88795 = 9001884 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 9001884)]) (.cons c88795_0 (.nil)) (by decide) (by decide))

theorem cover88796 : P.CoversSplit 26 10 88796 0xffff0000fffc0504ffff0000fffc050000000000000000000000000030300000050505050504050400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 587, 874, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c88796_0 : P.sumLeaves 26 90927104 768 = 96000 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88796) (lo := 0) (len := 768) (W := 96000) check rows elimOK (by decide) (by decide) cover88796 (by decide)
  decide +kernel

theorem contract88796_1 : P.leaf 32 1420748 = 17088 := by
  exact leaf_contract_factors (k := 32) (b := 16) (H := 1420748) (ss := [(2, 1, 474), (7, 1, 487), (21, 1, 524), (9, 1, 473), (15, 1, 473), (11, 1, 817), (12, 1, 817), (19, 1, 865), (14, 1, 866), (10, 1, 867), (20, 1, 915), (30, 1, 1658), (32, 1, 1315), (29, 0, 1665), (33, 0, 1665), (27, 1, 538)]) (ids := [1, 2, 3, 4, 6, 11, 14, 15, 16, 20, 22, 24, 26, 29, 21, 23]) (cs := [1, 2, 3, 4, 5, 1, 6, 1, 1, 1, 1, 7, 1, 1, 8, 9, 10, 1, 1, 1, 11, 16, 12, 17, 13, 1, 14, 0, 1, 15, 1, 0]) (bs := [14, 2]) (W := 17088) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c88796_1 : P.sumLeaves 26 90927872 64 = 17088 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1420748) rows (by decide) (by decide)).symm.trans contract88796_1

theorem c88796_2 : P.sumLeaves 26 90927936 192 = 3688946 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88796) (lo := 832) (len := 192) (W := 3688946) check rows elimOK (by decide) (by decide) cover88796 (by decide)
  decide +kernel

theorem h88796 : P.leaf 36 88796 = 3802034 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(768, 96000), (64, 17088), (192, 3688946)]) (.cons c88796_0 (.cons c88796_1 (.cons c88796_2 (.nil)))) (by decide) (by decide))

theorem cover88797 : P.CoversSplit 26 10 88797 0xffff0000fffc0504ffff0000fffc050000000000000000000000000030300000050505050504050400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 587, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c88797_0 : P.sumLeaves 26 90928128 1024 = 10326820 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88797) (lo := 0) (len := 1024) (W := 10326820) check rows elimOK (by decide) (by decide) cover88797 (by decide)
  decide +kernel

theorem h88797 : P.leaf 36 88797 = 10326820 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 10326820)]) (.cons c88797_0 (.nil)) (by decide) (by decide))

theorem cover88798 : P.CoversSplit 26 10 88798 0xffff0000fffc0504ffff0000fffc050000000000000000000000000030300000050505050504050400000000000000000000000000000000000000000000000000000000330001000000000033000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 587, 874, 922, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c88798_0 : P.sumLeaves 26 90929152 1024 = 22533872 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88798) (lo := 0) (len := 1024) (W := 22533872) check rows elimOK (by decide) (by decide) cover88798 (by decide)
  decide +kernel

theorem h88798 : P.leaf 36 88798 = 22533872 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 22533872)]) (.cons c88798_0 (.nil)) (by decide) (by decide))

theorem cover88799 : P.CoversSplit 26 10 88799 0xffff0000fffc0504ffff0000fffc050000000000000000000000000030300000050505050504050400000000000000000000000000000000000000000000000000000000330001000000000033000100000000000000000000000000000000000000000001000100000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 587, 922, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c88799_0 : P.sumLeaves 26 90930176 1024 = 52072398 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88799) (lo := 0) (len := 1024) (W := 52072398) check rows elimOK (by decide) (by decide) cover88799 (by decide)
  decide +kernel

theorem h88799 : P.leaf 36 88799 = 52072398 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 52072398)]) (.cons c88799_0 (.nil)) (by decide) (by decide))

theorem cover88806 : P.CoversSplit 26 10 88806 0xcc00cc00cc00c800cc00cc00cc00c80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003300320000000000330030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 524, 587, 874, 922, 972, 979, 1266, 1315]) (by decide +kernel)

theorem c88806_0 : P.sumLeaves 26 90937344 384 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88806) (lo := 0) (len := 384) (W := 0) check rows elimOK (by decide) (by decide) cover88806 (by decide)
  decide +kernel

theorem contract88806_1 : P.leaf 32 1420902 = 2702 := by
  exact leaf_contract_factors (k := 32) (b := 14) (H := 1420902) (ss := [(14, 1, 872), (12, 1, 929), (29, 0, 979), (9, 0, 587), (13, 6, 559), (31, 0, 587), (8, 1, 510), (33, 0, 979), (16, 1, 1210), (18, 1, 1210), (27, 1, 538), (19, 1, 1273), (4, 1, 572), (15, 1, 865), (21, 1, 1259), (6, 1, 475), (20, 0, 1665), (2, 1, 474)]) (ids := [1, 3, 5, 8, 9, 15, 20, 21, 23, 24, 26, 28, 30, 22]) (cs := [1, 2, 1, 3, 1, 4, 1, 0, 5, 6, 1, 1, 1, 1, 1, 7, 1, 1, 0, 1, 8, 9, 15, 10, 11, 1, 12, 0, 13, 0, 14, 0]) (bs := [13, 1]) (W := 2702) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c88806_1 : P.sumLeaves 26 90937728 64 = 2702 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1420902) rows (by decide) (by decide)).symm.trans contract88806_1

theorem c88806_2 : P.sumLeaves 26 90937792 576 = 1658270 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88806) (lo := 448) (len := 576) (W := 1658270) check rows elimOK (by decide) (by decide) cover88806 (by decide)
  decide +kernel

theorem h88806 : P.leaf 36 88806 = 1660972 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(384, 0), (64, 2702), (576, 1658270)]) (.cons c88806_0 (.cons c88806_1 (.cons c88806_2 (.nil)))) (by decide) (by decide))

theorem cover88807 : P.CoversSplit 26 10 88807 0xcc00cc00cc00c800cc00cc00cc00c80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003300320000000000330030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 587, 922, 972, 979, 1266, 1315]) (by decide +kernel)

theorem c88807_0 : P.sumLeaves 26 90938368 1024 = 3579156 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88807) (lo := 0) (len := 1024) (W := 3579156) check rows elimOK (by decide) (by decide) cover88807 (by decide)
  decide +kernel

theorem h88807 : P.leaf 36 88807 = 3579156 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3579156)]) (.cons c88807_0 (.nil)) (by decide) (by decide))

theorem cover88810 : P.CoversSplit 26 10 88810 0xf0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300030000000000030003000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 524, 874, 972, 979, 1266, 1665]) (by decide +kernel)

theorem c88810_0 : P.sumLeaves 26 90941440 384 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88810) (lo := 0) (len := 384) (W := 0) check rows elimOK (by decide) (by decide) cover88810 (by decide)
  decide +kernel

theorem contract88810_1 : P.leaf 32 1420966 = 3192 := by
  exact leaf_contract_factors (k := 32) (b := 16) (H := 1420966) (ss := [(19, 1, 466), (2, 1, 482), (14, 1, 872), (15, 1, 865), (12, 1, 929), (16, 1, 1210), (18, 1, 1210), (21, 1, 1259), (20, 0, 1665), (4, 1, 572), (9, 0, 1609), (29, 0, 1665), (31, 1, 587), (30, 1, 972), (33, 0, 1665), (27, 1, 538)]) (ids := [1, 3, 4, 5, 6, 8, 9, 11, 15, 20, 21, 22, 24, 26, 30, 23]) (cs := [1, 2, 1, 3, 4, 5, 6, 0, 7, 8, 1, 9, 1, 1, 1, 10, 1, 1, 0, 1, 11, 12, 13, 17, 14, 1, 15, 0, 1, 1, 16, 0]) (bs := [15, 1]) (W := 3192) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c88810_1 : P.sumLeaves 26 90941824 64 = 3192 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1420966) rows (by decide) (by decide)).symm.trans contract88810_1

theorem c88810_2 : P.sumLeaves 26 90941888 576 = 1562816 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88810) (lo := 448) (len := 576) (W := 1562816) check rows elimOK (by decide) (by decide) cover88810 (by decide)
  decide +kernel

theorem h88810 : P.leaf 36 88810 = 1566008 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(384, 0), (64, 3192), (576, 1562816)]) (.cons c88810_0 (.cons c88810_1 (.cons c88810_2 (.nil)))) (by decide) (by decide))

theorem cover88811 : P.CoversSplit 26 10 88811 0xf0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f000000000000000000000000030303000000000000000000000000000000000000000000000000000000000000000000000000000300030000000000030003000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 587, 922, 972, 979, 1266, 1273, 1322, 1658, 1665]) (by decide +kernel)

theorem c88811_0 : P.sumLeaves 26 90942464 1024 = 5368073 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88811) (lo := 0) (len := 1024) (W := 5368073) check rows elimOK (by decide) (by decide) cover88811 (by decide)
  decide +kernel

theorem h88811 : P.leaf 36 88811 = 5368073 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5368073)]) (.cons c88811_0 (.nil)) (by decide) (by decide))

theorem cover88814 : P.CoversSplit 26 10 88814 0xfffffffffffcfaf8fffffffafffcfaf800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000330032000000000033003200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [524, 874, 922, 972, 979, 1266, 1315, 1665]) (by decide +kernel)

theorem c88814_0 : P.sumLeaves 26 90945536 384 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88814) (lo := 0) (len := 384) (W := 0) check rows elimOK (by decide) (by decide) cover88814 (by decide)
  decide +kernel

theorem contract88814_1 : P.leaf 32 1421030 = 11600 := by
  exact leaf_contract_factors (k := 32) (b := 17) (H := 1421030) (ss := [(14, 1, 872), (12, 1, 929), (16, 1, 1210), (18, 1, 1210), (20, 0, 1665), (2, 1, 474), (9, 0, 1609), (29, 0, 1665), (31, 1, 587), (33, 0, 1665), (27, 1, 538), (19, 1, 1273), (4, 1, 572), (15, 1, 865), (21, 1, 1259)]) (ids := [1, 3, 4, 5, 6, 8, 9, 11, 15, 20, 21, 22, 24, 26, 28, 30, 23]) (cs := [1, 2, 1, 3, 4, 5, 6, 0, 7, 8, 1, 9, 1, 1, 1, 10, 1, 1, 0, 1, 11, 12, 13, 18, 14, 1, 15, 0, 16, 1, 17, 0]) (bs := [16, 1]) (W := 11600) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c88814_1 : P.sumLeaves 26 90945920 64 = 11600 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1421030) rows (by decide) (by decide)).symm.trans contract88814_1

theorem c88814_2 : P.sumLeaves 26 90945984 553 = 4677923 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88814) (lo := 448) (len := 553) (W := 4677923) check rows elimOK (by decide) (by decide) cover88814 (by decide)
  decide +kernel

theorem c88814_3 : P.sumLeaves 26 90946537 23 = 2702204 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88814) (lo := 1001) (len := 23) (W := 2702204) check rows elimOK (by decide) (by decide) cover88814 (by decide)
  decide +kernel

theorem h88814 : P.leaf 36 88814 = 7391727 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(384, 0), (64, 11600), (553, 4677923), (23, 2702204)]) (.cons c88814_0 (.cons c88814_1 (.cons c88814_2 (.cons c88814_3 (.nil))))) (by decide) (by decide))

theorem cover88815 : P.CoversSplit 26 10 88815 0xfffffffffffcfaf8fffffffafffcfaf800000000000000000000000030303000000000000000000000000000000000000000000000000000000000000000000000000000330032000000000033003200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 922, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c88815_0 : P.sumLeaves 26 90946560 988 = 9700275 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88815) (lo := 0) (len := 988) (W := 9700275) check rows elimOK (by decide) (by decide) cover88815 (by decide)
  decide +kernel

theorem c88815_1 : P.sumLeaves 26 90947548 36 = 7070684 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88815) (lo := 988) (len := 36) (W := 7070684) check rows elimOK (by decide) (by decide) cover88815 (by decide)
  decide +kernel

theorem h88815 : P.leaf 36 88815 = 16770959 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(988, 9700275), (36, 7070684)]) (.cons c88815_0 (.cons c88815_1 (.nil))) (by decide) (by decide))

theorem cover88820 : P.CoversSplit 26 10 88820 0xcc00cc00cc00c800cc00cc00cc00c80000000000000000000000000000000000cc00c800cc00c800c000c000c000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 559, 587, 874, 922, 923, 972, 979, 1315]) (by decide +kernel)

theorem c88820_0 : P.sumLeaves 26 90951680 1024 = 657452 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88820) (lo := 0) (len := 1024) (W := 657452) check rows elimOK (by decide) (by decide) cover88820 (by decide)
  decide +kernel

theorem h88820 : P.leaf 36 88820 = 657452 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 657452)]) (.cons c88820_0 (.nil)) (by decide) (by decide))

theorem cover88821 : P.CoversSplit 26 10 88821 0xcc00cc00cc00c800cc00cc00cc00c80000000000000000000000000000000000cc00c800cc00c800c000c000c000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 559, 587, 922, 923, 972, 979, 1315]) (by decide +kernel)

theorem c88821_0 : P.sumLeaves 26 90952704 1024 = 2720324 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88821) (lo := 0) (len := 1024) (W := 2720324) check rows elimOK (by decide) (by decide) cover88821 (by decide)
  decide +kernel

theorem h88821 : P.leaf 36 88821 = 2720324 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2720324)]) (.cons c88821_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(88703, 360), (88770, 120), (88771, 720), (88775, 720), (88778, 720), (88779, 720), (88782, 720), (88783, 720), (88788, 360), (88789, 720), (88790, 720), (88791, 720), (88793, 360), (88794, 720), (88795, 720), (88796, 720), (88797, 720), (88798, 720), (88799, 720), (88806, 720), (88807, 720), (88810, 720), (88811, 720), (88814, 720), (88815, 720), (88820, 360), (88821, 720)]

theorem segOK : checkSeg 20 perms 88703 88822 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 88703 88822 17400 125294724120 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 125294724120)
    (SegSum.cons (w := 360) h88703 (SegSum.cons (w := 120) h88770 (SegSum.cons (w := 720) h88771 (SegSum.cons (w := 720) h88775 (SegSum.cons (w := 720) h88778 (SegSum.cons (w := 720) h88779 (SegSum.cons (w := 720) h88782 (SegSum.cons (w := 720) h88783 (SegSum.cons (w := 360) h88788 (SegSum.cons (w := 720) h88789 (SegSum.cons (w := 720) h88790 (SegSum.cons (w := 720) h88791 (SegSum.cons (w := 360) h88793 (SegSum.cons (w := 720) h88794 (SegSum.cons (w := 720) h88795 (SegSum.cons (w := 720) h88796 (SegSum.cons (w := 720) h88797 (SegSum.cons (w := 720) h88798 (SegSum.cons (w := 720) h88799 (SegSum.cons (w := 720) h88806 (SegSum.cons (w := 720) h88807 (SegSum.cons (w := 720) h88810 (SegSum.cons (w := 720) h88811 (SegSum.cons (w := 720) h88814 (SegSum.cons (w := 720) h88815 (SegSum.cons (w := 360) h88820 (SegSum.cons (w := 720) h88821 (show SegSum (P.leaf 36) [] 0 from rfl)))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S57
