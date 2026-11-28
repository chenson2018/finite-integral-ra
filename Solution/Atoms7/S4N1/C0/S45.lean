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

namespace RACert.S4N1.C0.S45

open RACert RACert.Problem

theorem cover7627 : P.CoversSplit 24 10 7627 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 516, 522, 523, 858, 865, 1209, 1217, 1258, 1272]) (by decide +kernel)

theorem h7627 : P.leaf 34 7627 = 521148 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 7627) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 7627) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7627) (weight := rowWeight keep5 twice5) (xs := [208, 511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover7627 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7628 : P.CoversSplit 24 10 7628 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h7628 : P.leaf 34 7628 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7628) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7628) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover7628 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7629 : P.CoversSplit 24 10 7629 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 523, 858, 865, 916, 1209, 1258, 1272]) (by decide +kernel)

theorem h7629 : P.leaf 34 7629 = 1188401 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7629) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7629) (weight := fun _ => 1) (xs := [511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover7629 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7631 : P.CoversSplit 24 10 7631 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 516, 522, 523, 858, 865, 1209, 1217, 1258, 1272]) (by decide +kernel)

theorem h7631 : P.leaf 34 7631 = 2224851 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 7631) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 7631) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7631) (weight := rowWeight keep5 twice5) (xs := [208, 511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover7631 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover19851 : P.CoversSplit 24 10 19851 0xaa000000a0000a000000000000000000aa0000000000000000000000000000008800000080000800220000002000000088000000000000002200000000000000aa000000a0000a000000000000000000aa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 516, 522, 865, 1202, 1210, 1259, 1601]) (ps := [(3, [502], [472])]) (by decide +kernel)

noncomputable def f19851 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (20327424 + i)

theorem c19851_0 : rowSum f19851 0 1024 = 1192068 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 19851) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover19851 (by decide)
  decide +kernel

theorem sum19851 : rowSum f19851 0 1024 = 1192068 :=
  c19851_0

theorem h19851 : P.leaf 34 19851 = 1192068 :=
  leaf_weighted (k := 24) (d := 10) (H := 19851) (keep := keep5) (twice := twice5) rows (by decide) (by decide) (bal5) (invRow5 (H := 19851) (by decide) (by decide +kernel)) sum19851

theorem h7633 : P.leaf 34 7633 = 1192068 :=
  orient4 (v := 19851) (by decide) (by decide +kernel) h19851

theorem cover51471 : P.CoversSplit 24 10 51471 0xaa000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 516, 517, 522, 528, 572, 859, 865, 879, 915, 921]) (by decide +kernel)

theorem h51471 : P.leaf 34 51471 = 1062300 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 51471) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 51471) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 51471) (weight := rowWeight keep4 twice4) (xs := [383, 507, 511, 893, 895, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover51471 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h7634 : P.leaf 34 7634 = 1062300 :=
  orient24 (v := 51471) (by decide) (by decide +kernel) h51471

theorem cover51487 : P.CoversSplit 24 10 51487 0xff00fa00fa000a00ff00fa00fa000a00f500f00040000000f500f000400000000000000000000000000000000000000000000000000000000000000000000000f000f000f0000000f000f000f0000000f000f00050000000f000f000500000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 529, 572, 858, 859, 866, 879, 915, 921, 1202]) (ps := [(8, [537], [565])]) (by decide +kernel)

theorem c51487_0 : P.sumLeaves 24 52722688 1001 = 9666919 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 51487) (lo := 0) (len := 1001) (W := 9666919) check rows elimOK (by decide) (by decide) cover51487 (by decide)
  decide +kernel

theorem c51487_1 : P.sumLeaves 24 52723689 23 = 4999458 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 51487) (lo := 1001) (len := 23) (W := 4999458) check rows elimOK (by decide) (by decide) cover51487 (by decide)
  decide +kernel

theorem h51487 : P.leaf 34 51487 = 14666377 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1001, 9666919), (23, 4999458)]) (.cons c51487_0 (.cons c51487_1 (.nil))) (by decide) (by decide))

theorem h7635 : P.leaf 34 7635 = 14666377 :=
  orient24 (v := 51487) (by decide) (by decide +kernel) h51487

theorem cover7636 : P.CoversSplit 24 10 7636 0xf0000000000000000000000000000000a0000000000000000000000000000000c000000000000000c00000000000000080000000000000008000000000000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 516, 858, 865, 866, 916, 1202, 1210, 1251, 1259, 1601]) (ps := [(8, [1272], [1266])]) (by decide +kernel)

theorem h7636 : P.leaf 34 7636 = 685728 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7636) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7636) (weight := fun _ => 1) (xs := [508, 509, 510, 511, 575, 639, 702, 703, 766, 767, 893, 895, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover7636 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7637 : P.CoversSplit 24 10 7637 0xff000000000000000000000000000000ff000000000000000000000000000000cc030000000000000000000000000000cc030000000000000000000000000000ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 516, 858, 865, 866, 916, 1202, 1209, 1210, 1251, 1601]) (ps := [(8, [1272], [1266])]) (by decide +kernel)

theorem c7637_0 : P.sumLeaves 24 7820288 1024 = 6470872 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7637) (lo := 0) (len := 1024) (W := 6470872) check rows elimOK (by decide) (by decide) cover7637 (by decide)
  decide +kernel

theorem h7637 : P.leaf 34 7637 = 6470872 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6470872)]) (.cons c7637_0 (.nil)) (by decide) (by decide))

theorem cover51503 : P.CoversSplit 24 10 51503 0xff00fa00fa00a0000000000000000000ff00fa00fa00a0000000000000000000000000000000000000000000000000000000000000000000000000000000000088008800880080000000000000000000880088008800800000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 529, 572, 858, 859, 865, 915, 921, 1202]) (by decide +kernel)

theorem c51503_0 : P.sumLeaves 24 52739072 1024 = 11715344 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 51503) (lo := 0) (len := 1024) (W := 11715344) check rows elimOK (by decide) (by decide) cover51503 (by decide)
  decide +kernel

theorem h51503 : P.leaf 34 51503 = 11715344 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 11715344)]) (.cons c51503_0 (.nil)) (by decide) (by decide))

theorem h7638 : P.leaf 34 7638 = 11715344 :=
  orient24 (v := 51503) (by decide) (by decide +kernel) h51503

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

theorem h7640 : P.leaf 34 7640 = 799912 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7640) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7640) (weight := fun _ => 1) (xs := [190, 191, 508, 509, 510, 511, 575, 639, 702, 703, 766, 767, 893, 895, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover7640 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7641 : P.CoversSplit 24 10 7641 0xff000000000000000000000000000000ff000000000000000000000000000000cc030000000000000000000000000000cc030000000000000000000000000000ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 516, 858, 865, 867, 916, 1202, 1209, 1210, 1251, 1601]) (ps := [(8, [1272], [1266])]) (by decide +kernel)

theorem c7641_0 : P.sumLeaves 24 7824384 1024 = 4548004 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7641) (lo := 0) (len := 1024) (W := 4548004) check rows elimOK (by decide) (by decide) cover7641 (by decide)
  decide +kernel

theorem h7641 : P.leaf 34 7641 = 4548004 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4548004)]) (.cons c7641_0 (.nil)) (by decide) (by decide))

theorem cover51535 : P.CoversSplit 24 10 51535 0xff00fa00fa0000000000000000000000a500a0000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00c800c80000000000000000000000840080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 516, 522, 572, 858, 859, 865, 879, 915, 921, 1202, 1217]) (by decide +kernel)

theorem c51535_0 : P.sumLeaves 24 52771840 1024 = 4389888 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 51535) (lo := 0) (len := 1024) (W := 4389888) check rows elimOK (by decide) (by decide) cover51535 (by decide)
  decide +kernel

theorem h51535 : P.leaf 34 51535 = 4389888 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4389888)]) (.cons c51535_0 (.nil)) (by decide) (by decide))

theorem h7642 : P.leaf 34 7642 = 4389888 :=
  orient24 (v := 51535) (by decide) (by decide +kernel) h51535

theorem cover51551 : P.CoversSplit 24 10 51551 0xff00fa00fa000000ff00fa00fa000000f500f00040000000f500f000400000000000000000000000000000000000000000000000000000000000000000000000f000f000f0000000f000f000f0000000f000f00050000000f000f000500000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 572, 858, 859, 866, 879, 915, 921, 1202]) (ps := [(8, [537], [565])]) (by decide +kernel)

theorem c51551_0 : P.sumLeaves 24 52788224 1006 = 17156834 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 51551) (lo := 0) (len := 1006) (W := 17156834) check rows elimOK (by decide) (by decide) cover51551 (by decide)
  decide +kernel

theorem c51551_1 : P.sumLeaves 24 52789230 18 = 4964778 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 51551) (lo := 1006) (len := 18) (W := 4964778) check rows elimOK (by decide) (by decide) cover51551 (by decide)
  decide +kernel

theorem h51551 : P.leaf 34 51551 = 22121612 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1006, 17156834), (18, 4964778)]) (.cons c51551_0 (.cons c51551_1 (.nil))) (by decide) (by decide))

theorem h7643 : P.leaf 34 7643 = 22121612 :=
  orient24 (v := 51551) (by decide) (by decide +kernel) h51551

theorem cover7644 : P.CoversSplit 24 10 7644 0xf0000000000000000000000000000000a0000000000000000000000000000000c000000000000000c00000000000000080000000000000008000000000000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 516, 858, 865, 916, 1202, 1210, 1251, 1259, 1601]) (ps := [(8, [1272], [1266])]) (by decide +kernel)

theorem h7644 : P.leaf 34 7644 = 2886732 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7644) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7644) (weight := fun _ => 1) (xs := [508, 509, 510, 511, 575, 639, 702, 703, 766, 767, 893, 895, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover7644 (by decide) (by decide) (by decide +kernel)
  decide +kernel

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

theorem h7648 : P.leaf 34 7648 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7648) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7648) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover7648 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7649 : P.CoversSplit 24 10 7649 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 858, 865, 916, 1209, 1258, 1266]) (by decide +kernel)

theorem h7649 : P.leaf 34 7649 = 274472 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7649) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7649) (weight := fun _ => 1) (xs := [511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover7649 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7650 : P.CoversSplit 24 10 7650 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 522, 858, 865, 1209, 1217, 1258, 1266]) (by decide +kernel)

theorem h7650 : P.leaf 34 7650 = 159616 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7650) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7650) (weight := fun _ => 1) (xs := [208, 511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover7650 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7651 : P.CoversSplit 24 10 7651 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 858, 865, 867, 916, 1209, 1217, 1258, 1266]) (by decide +kernel)

theorem h7651 : P.leaf 34 7651 = 1987024 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7651) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7651) (weight := fun _ => 1) (xs := [208, 511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover7651 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7652 : P.CoversSplit 24 10 7652 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h7652 : P.leaf 34 7652 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7652) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7652) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover7652 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7653 : P.CoversSplit 24 10 7653 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 858, 865, 916, 1209, 1258, 1266]) (by decide +kernel)

theorem h7653 : P.leaf 34 7653 = 871068 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7653) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7653) (weight := fun _ => 1) (xs := [511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover7653 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7654 : P.CoversSplit 24 10 7654 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 522, 858, 865, 1209, 1217, 1258, 1266]) (by decide +kernel)

theorem h7654 : P.leaf 34 7654 = 2830112 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7654) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7654) (weight := fun _ => 1) (xs := [208, 511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover7654 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7655 : P.CoversSplit 24 10 7655 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 858, 865, 867, 916, 1209, 1217, 1258, 1266]) (by decide +kernel)

theorem h7655 : P.leaf 34 7655 = 5027810 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7655) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7655) (weight := fun _ => 1) (xs := [208, 511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover7655 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7656 : P.CoversSplit 24 10 7656 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h7656 : P.leaf 34 7656 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7656) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7656) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover7656 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7657 : P.CoversSplit 24 10 7657 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 858, 865, 916, 1209, 1258, 1266]) (by decide +kernel)

theorem h7657 : P.leaf 34 7657 = 1069992 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7657) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7657) (weight := fun _ => 1) (xs := [511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover7657 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7658 : P.CoversSplit 24 10 7658 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 522, 858, 865, 1209, 1217, 1258, 1266]) (by decide +kernel)

theorem h7658 : P.leaf 34 7658 = 1232828 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7658) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7658) (weight := fun _ => 1) (xs := [208, 511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover7658 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7659 : P.CoversSplit 24 10 7659 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 858, 865, 867, 916, 1209, 1217, 1258, 1266]) (by decide +kernel)

theorem h7659 : P.leaf 34 7659 = 2122130 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7659) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7659) (weight := fun _ => 1) (xs := [208, 511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover7659 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7660 : P.CoversSplit 24 10 7660 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h7660 : P.leaf 34 7660 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7660) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7660) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover7660 (by decide) (by decide) (by decide +kernel)
  decide +kernel

def seg : List (ℕ × ℕ) := [(7627, 24), (7628, 24), (7629, 48), (7631, 24), (7633, 24), (7634, 24), (7635, 48), (7636, 48), (7637, 48), (7638, 48), (7639, 48), (7640, 48), (7641, 48), (7642, 48), (7643, 48), (7644, 48), (7645, 48), (7646, 48), (7647, 48), (7648, 24), (7649, 48), (7650, 48), (7651, 48), (7652, 48), (7653, 48), (7654, 48), (7655, 48), (7656, 48), (7657, 48), (7658, 48), (7659, 48), (7660, 48)]

theorem segOK : checkSeg 16 perms 7627 7661 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 7627 7661 1392 12010379160 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 12010379160)
    (SegSum.cons (w := 24) h7627 (SegSum.cons (w := 24) h7628 (SegSum.cons (w := 48) h7629 (SegSum.cons (w := 24) h7631 (SegSum.cons (w := 24) h7633 (SegSum.cons (w := 24) h7634 (SegSum.cons (w := 48) h7635 (SegSum.cons (w := 48) h7636 (SegSum.cons (w := 48) h7637 (SegSum.cons (w := 48) h7638 (SegSum.cons (w := 48) h7639 (SegSum.cons (w := 48) h7640 (SegSum.cons (w := 48) h7641 (SegSum.cons (w := 48) h7642 (SegSum.cons (w := 48) h7643 (SegSum.cons (w := 48) h7644 (SegSum.cons (w := 48) h7645 (SegSum.cons (w := 48) h7646 (SegSum.cons (w := 48) h7647 (SegSum.cons (w := 24) h7648 (SegSum.cons (w := 48) h7649 (SegSum.cons (w := 48) h7650 (SegSum.cons (w := 48) h7651 (SegSum.cons (w := 48) h7652 (SegSum.cons (w := 48) h7653 (SegSum.cons (w := 48) h7654 (SegSum.cons (w := 48) h7655 (SegSum.cons (w := 48) h7656 (SegSum.cons (w := 48) h7657 (SegSum.cons (w := 48) h7658 (SegSum.cons (w := 48) h7659 (SegSum.cons (w := 48) h7660 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S45
