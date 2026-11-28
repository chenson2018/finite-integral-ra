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

namespace RACert.S4N1.C0.S11

open RACert RACert.Problem

theorem cover1485 : P.CoversSplit 24 10 1485 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h1485 : P.leaf 34 1485 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1485) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1485) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1485 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1486 : P.CoversSplit 24 10 1486 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h1486 : P.leaf 34 1486 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1486) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1486) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1486 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1487 : P.CoversSplit 24 10 1487 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h1487 : P.leaf 34 1487 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1487) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1487) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1487 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover16687 : P.CoversSplit 24 10 16687 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 529, 572, 858, 859, 860, 865, 872, 915]) (by decide +kernel)

theorem h16687 : P.leaf 34 16687 = 220136 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 16687) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 16687) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 16687) (weight := rowWeight keep1 twice1) (xs := [383, 511, 895, 1023]) check rows elimOK (by decide) (by decide) cover16687 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1494 : P.leaf 34 1494 = 220136 :=
  orient24 (v := 16687) (by decide) (by decide +kernel) h16687

theorem cover16703 : P.CoversSplit 24 10 16703 0xf000f00000000000f000f00000000000f000f00000000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000f000f00000000000f000000000000000f000f00000000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 529, 572, 858, 859, 860, 865, 866, 871, 872, 915, 921, 1251, 1264]) (by decide +kernel)

noncomputable def f16703 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (17103872 + i)

theorem c16703_0 : rowSum f16703 0 1024 = 5481092 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 16703) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover16703 (by decide)
  decide +kernel

theorem sum16703 : rowSum f16703 0 1024 = 5481092 :=
  c16703_0

theorem h16703 : P.leaf 34 16703 = 5481092 :=
  leaf_weighted (k := 24) (d := 10) (H := 16703) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 16703) (by decide) (by decide +kernel)) sum16703

theorem h1495 : P.leaf 34 1495 = 5481092 :=
  orient24 (v := 16703) (by decide) (by decide +kernel) h16703

theorem cover1500 : P.CoversSplit 24 10 1500 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h1500 : P.leaf 34 1500 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1500) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1500) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1500 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1501 : P.CoversSplit 24 10 1501 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem h1501 : P.leaf 34 1501 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1501) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1501) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1501 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover16751 : P.CoversSplit 24 10 16751 0xc0004000800000000000000000000000c00000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000c0004000800000000000000000000000c00040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 572, 858, 859, 865, 872, 915, 916, 1202, 1210, 1308]) (by decide +kernel)

theorem h16751 : P.leaf 34 16751 = 684316 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 16751) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 16751) (weight := fun _ => 1) (xs := [366, 382, 383, 479, 494, 510, 511, 846, 894, 895, 991, 1006, 1022, 1023]) check rows elimOK (by decide) (by decide) cover16751 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1502 : P.leaf 34 1502 = 684316 :=
  orient24 (v := 16751) (by decide) (by decide +kernel) h16751

theorem cover16767 : P.CoversSplit 24 10 16767 0xf000f000a000a000f000f000a000a000f000f000a000a000f000f000a000a0000000000000000000000000000000000000000000000000000000000000000000f000f000a000a000f0000000a0000000f000f00000000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [572, 858, 859, 865, 866, 915, 916, 921, 1202, 1210, 1264, 1308]) (by decide +kernel)

theorem c16767_0 : P.sumLeaves 24 17169408 1024 = 13611342 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 16767) (lo := 0) (len := 1024) (W := 13611342) check rows elimOK (by decide) (by decide) cover16767 (by decide)
  decide +kernel

theorem h16767 : P.leaf 34 16767 = 13611342 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 13611342)]) (.cons c16767_0 (.nil)) (by decide) (by decide))

theorem h1503 : P.leaf 34 1503 = 13611342 :=
  orient24 (v := 16767) (by decide) (by decide +kernel) h16767

theorem cover1516 : P.CoversSplit 24 10 1516 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h1516 : P.leaf 34 1516 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1516) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1516) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1516 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1517 : P.CoversSplit 24 10 1517 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h1517 : P.leaf 34 1517 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1517) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1517) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1517 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1518 : P.CoversSplit 24 10 1518 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h1518 : P.leaf 34 1518 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1518) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1518) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1518 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1519 : P.CoversSplit 24 10 1519 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h1519 : P.leaf 34 1519 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1519) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1519) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1519 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover16879 : P.CoversSplit 24 10 16879 0xf0015501a00000003031111120200000f0010000000050003031000000000000c0004400800000000000000000000000c0000000000040000000000000000000f0015501a00000000000000000000000f00155010000500030311111000010100000000000000000300000002000000000000000000000003000110000001000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 858, 859, 865, 1202, 1210, 1259, 1601]) (ps := [(17, [1259], [1251]), (18, [1210], [1264])]) (by decide +kernel)

noncomputable def f16879 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (17284096 + i)

theorem c16879_0 : rowSum f16879 0 1024 = 3131569 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 16879) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover16879 (by decide)
  decide +kernel

theorem sum16879 : rowSum f16879 0 1024 = 3131569 :=
  c16879_0

theorem h16879 : P.leaf 34 16879 = 3131569 :=
  leaf_weighted (k := 24) (d := 10) (H := 16879) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 16879) (by decide) (by decide +kernel)) sum16879

theorem h1534 : P.leaf 34 1534 = 3131569 :=
  orient24 (v := 16879) (by decide) (by decide +kernel) h16879

theorem cover16895 : P.CoversSplit 24 10 16895 0xfff8faf8aaa8aaa8ffc8fac8aa88aa88fff8faf8aaa8aaa8ffc8fac8aa88aa88ccc8c8c888888888ccc8c8c888888888ccc8c8c888888888ccc8c8c888888888fff8faf8aaa8aaa8ffc8fac8aa88aa88fff8faf8aaa8aaa8ffc8fac8aa88aa88ccc8c8c888888888ccc8c8c888888888ccc8c8c888888888ccc8c8c888888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [858, 859, 865, 915, 1202, 1210, 1259, 1601]) (by decide +kernel)

noncomputable def f16895 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (17300480 + i)

theorem c16895_0 : rowSum f16895 0 372 = 36670574 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 16895) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover16895 (by decide)
  decide +kernel

theorem c16895_1 : rowSum f16895 372 331 = 75028615 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 16895) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover16895 (by decide)
  decide +kernel

theorem c16895_2 : rowSum f16895 703 321 = 57628754 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 16895) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover16895 (by decide)
  decide +kernel

theorem sum16895 : rowSum f16895 0 1024 = 169327943 :=
  rowSum_append (F := f16895) (lo := 0) (n := 372) (m := 652) (A := 36670574) (B := 132657369) c16895_0 (rowSum_append (F := f16895) (lo := 372) (n := 331) (m := 321) (A := 75028615) (B := 57628754) c16895_1 (c16895_2))

theorem h16895 : P.leaf 34 16895 = 169327943 :=
  leaf_weighted (k := 24) (d := 10) (H := 16895) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 16895) (by decide) (by decide +kernel)) sum16895

theorem h1535 : P.leaf 34 1535 = 169327943 :=
  orient24 (v := 16895) (by decide) (by decide +kernel) h16895

theorem cover33571 : P.CoversSplit 24 10 33571 0xf000f00000000000f000f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000c00000000000a000f000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [468, 474, 517, 529, 572, 871, 921]) (by decide +kernel)

theorem h33571 : P.leaf 34 33571 = 47517 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 33571) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 33571) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 33571) (weight := rowWeight keep1 twice1) (xs := [300, 301, 302, 303, 317, 319, 366, 367, 383, 940, 941, 942, 943, 956, 957, 958, 959, 1004, 1005, 1006, 1007, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover33571 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1590 : P.leaf 34 1590 = 47517 :=
  orient25 (v := 33571) (by decide) (by decide +kernel) h33571

theorem cover33587 : P.CoversSplit 24 10 33587 0xf000f00000000000f000f00000000000a000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000c000c0000000000000000000000000008000c00000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [468, 474, 517, 572, 871, 921, 1209, 1258]) (ps := [(16, [528, 1251], [1258])]) (by decide +kernel)

theorem h33587 : P.leaf 34 33587 = 152611 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 33587) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 33587) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 33587) (weight := rowWeight keep1 twice1) (xs := [317, 319, 366, 367, 383, 494, 495, 510, 511, 829, 831, 893, 895, 940, 941, 942, 943, 956, 957, 958, 959, 1004, 1005, 1006, 1007, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover33587 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1591 : P.leaf 34 1591 = 152611 :=
  orient25 (v := 33587) (by decide) (by decide +kernel) h33587

theorem cover2662 : P.CoversSplit 24 10 2662 0x8800000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000880000000000000000230000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 475, 515, 522, 524, 566, 572, 859, 916, 1210, 1258]) (ps := [(14, [880], [859, 915])]) (by decide +kernel)

theorem h2662 : P.leaf 34 2662 = 14370 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 2662) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 2662) (weight := fun _ => 1) (xs := [304, 305, 309, 379, 383, 507, 511, 895, 1019, 1023]) check rows elimOK (by decide) (by decide) cover2662 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1596 : P.leaf 34 1596 = 14370 :=
  orient4 (v := 2662) (by decide) (by decide +kernel) h2662

theorem cover1597 : P.CoversSplit 24 10 1597 0xcc000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000840000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 517, 524, 529, 572, 860, 915, 1209, 1251, 1258, 1259]) (ps := [(8, [531], [517, 572]), (16, [528], [1258])]) (by decide +kernel)

theorem h1597 : P.leaf 34 1597 = 156432 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 1597) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 1597) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1597) (weight := rowWeight keep2 twice2) (xs := [309, 378, 383, 506, 507, 510, 511, 895, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover1597 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1598 : P.CoversSplit 24 10 1598 0xcc000000000000000000000000000000800000000000000000000000000000000000000000000000003300000000000000000000000000000020000000000000cc000000000000000000000000000000840000000000000000210000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 517, 524, 529, 572, 860, 915, 1209, 1251, 1258, 1259]) (ps := [(8, [531], [517, 572])]) (by decide +kernel)

theorem h1598 : P.leaf 34 1598 = 257421 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 1598) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 1598) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1598) (weight := rowWeight keep2 twice2) (xs := [304, 309, 378, 383, 506, 507, 510, 511, 565, 688, 689, 692, 693, 895, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover1598 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1599 : P.CoversSplit 24 10 1599 0xcc000000000000000000000000000000800000000000000000000000000000000000000000000000003300000000000000000000000000000020000000000000cc000000000000000000000000000000840000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 524, 529, 572, 860, 915, 1209, 1251, 1258, 1259]) (ps := [(8, [531], [517, 572]), (16, [528], [1258])]) (by decide +kernel)

theorem h1599 : P.leaf 34 1599 = 664929 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 1599) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 1599) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1599) (weight := rowWeight keep2 twice2) (xs := [309, 378, 383, 506, 507, 510, 511, 565, 688, 689, 692, 693, 895, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover1599 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1622 : P.CoversSplit 24 10 1622 0xcc00cc00800000000000000000000000840084000000000000210021000000000000000000000000003300330000000000000000000000000021002100000000cc00cc00800000000000000000000000840084000400000000210021000100000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 475, 516, 572, 573, 860, 915, 916, 1202, 1209, 1217, 1258]) (by decide +kernel)

noncomputable def f1622 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 24 (1660928 + i)

theorem c1622_0 : rowSum f1622 0 1024 = 228129 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 1622) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover1622 (by decide)
  decide +kernel

theorem sum1622 : rowSum f1622 0 1024 = 228129 :=
  c1622_0

theorem h1622 : P.leaf 34 1622 = 228129 :=
  leaf_weighted (k := 24) (d := 10) (H := 1622) (keep := keep3) (twice := twice3) rows (by decide) (by decide) (bal3) (invRow3 (H := 1622) (by decide) (by decide +kernel)) sum1622

theorem cover1623 : P.CoversSplit 24 10 1623 0xcc00cc00800000000000000000000000cc00cc000000000000330033000000000000000000000000003300330000000000000000000000000033003300000000cc00cc00800000000000000000000000cc00cc008000000000330033002000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [475, 516, 572, 573, 915, 916, 1202, 1209, 1217, 1258]) (by decide +kernel)

noncomputable def f1623 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 24 (1661952 + i)

theorem c1623_0 : rowSum f1623 0 1024 = 1345950 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 1623) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover1623 (by decide)
  decide +kernel

theorem sum1623 : rowSum f1623 0 1024 = 1345950 :=
  c1623_0

theorem h1623 : P.leaf 34 1623 = 1345950 :=
  leaf_weighted (k := 24) (d := 10) (H := 1623) (keep := keep3) (twice := twice3) rows (by decide) (by decide) (bal3) (invRow3 (H := 1623) (by decide) (by decide +kernel)) sum1623

theorem cover2666 : P.CoversSplit 24 10 2666 0x8800000000000000000000000000000080000000000000000021000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000800000000000000000210000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 474, 515, 522, 523, 572, 573, 859, 915, 1209, 1210, 1251, 1258]) (by decide +kernel)

theorem h2666 : P.leaf 34 2666 = 31492 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 2666) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 2666) (weight := fun _ => 1) (xs := [304, 309, 383, 507, 511, 816, 821, 895, 1019, 1023]) check rows elimOK (by decide) (by decide) cover2666 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1628 : P.leaf 34 1628 = 31492 :=
  orient4 (v := 2666) (by decide) (by decide +kernel) h2666

theorem cover2667 : P.CoversSplit 24 10 2667 0xcc000000000000000000000000000000cc0000000000000000320000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000cc0000000000000000320000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [474, 515, 522, 523, 572, 573, 859, 915, 1202, 1209, 1210, 1251, 1258]) (by decide +kernel)

theorem h2667 : P.leaf 34 2667 = 379640 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 2667) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 2667) (weight := fun _ => 1) (xs := [305, 308, 309, 378, 379, 382, 383, 506, 507, 510, 511, 817, 820, 821, 890, 891, 894, 895, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover2667 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1629 : P.leaf 34 1629 = 379640 :=
  orient4 (v := 2667) (by decide) (by decide +kernel) h2667

theorem cover1630 : P.CoversSplit 24 10 1630 0xcc00cc00800000000000000000000000840084000000000000210021000000000000000000000000003300330000000000000000000000000021002100000000cc00cc00800000000000000000000000840084000400000000210021000100000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 516, 523, 572, 573, 860, 915, 1202, 1209, 1217, 1258]) (by decide +kernel)

noncomputable def f1630 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 24 (1669120 + i)

theorem c1630_0 : rowSum f1630 0 1024 = 562375 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 1630) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover1630 (by decide)
  decide +kernel

theorem sum1630 : rowSum f1630 0 1024 = 562375 :=
  c1630_0

theorem h1630 : P.leaf 34 1630 = 562375 :=
  leaf_weighted (k := 24) (d := 10) (H := 1630) (keep := keep3) (twice := twice3) rows (by decide) (by decide) (bal3) (invRow3 (H := 1630) (by decide) (by decide +kernel)) sum1630

theorem cover1631 : P.CoversSplit 24 10 1631 0xcc00cc00800000000000000000000000cc00cc000000000000330033000000000000000000000000003300330000000000000000000000000033003300000000cc00cc00800000000000000000000000cc00cc008000000000330033002000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [516, 523, 572, 573, 915, 1202, 1209, 1217, 1258]) (by decide +kernel)

noncomputable def f1631 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 24 (1670144 + i)

theorem c1631_0 : rowSum f1631 0 1024 = 1968532 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 1631) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover1631 (by decide)
  decide +kernel

theorem sum1631 : rowSum f1631 0 1024 = 1968532 :=
  c1631_0

theorem h1631 : P.leaf 34 1631 = 1968532 :=
  leaf_weighted (k := 24) (d := 10) (H := 1631) (keep := keep3) (twice := twice3) rows (by decide) (by decide) (bal3) (invRow3 (H := 1631) (by decide) (by decide +kernel)) sum1631

theorem cover1644 : P.CoversSplit 24 10 1644 0x8800000000000000000000000000000080000000000000000000000000000000000000000000000000110000000000000000000000000000001100000000000088000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 522, 572, 860, 872, 915, 1202, 1209, 1251]) (by decide +kernel)

theorem h1644 : P.leaf 34 1644 = 13898 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1644) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1644) (weight := fun _ => 1) (xs := [383, 507, 511, 560, 564, 688, 692, 895, 1019, 1023]) check rows elimOK (by decide) (by decide) cover1644 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3179 : P.CoversSplit 24 10 3179 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000210000002100000000000000000000002100000021000080000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [417, 515, 522, 523, 565, 572, 858, 865, 1209, 1217]) (ps := [(5, [426], [474])]) (by decide +kernel)

theorem h3179 : P.leaf 34 3179 = 102551 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3179) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3179) (weight := fun _ => 1) (xs := [383, 511, 528, 533, 560, 565, 656, 661, 688, 693, 895, 1023]) check rows elimOK (by decide) (by decide) cover3179 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1645 : P.leaf 34 1645 = 102551 :=
  orient5 (v := 3179) (by decide) (by decide +kernel) h3179

theorem cover1646 : P.CoversSplit 24 10 1646 0x8800000000000000000000000000000080000000000000000021000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000800000000000000000210000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 522, 572, 860, 872, 915, 1209, 1210, 1251, 1258]) (by decide +kernel)

theorem h1646 : P.leaf 34 1646 = 130896 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1646) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1646) (weight := fun _ => 1) (xs := [304, 309, 383, 507, 511, 816, 821, 895, 1019, 1023]) check rows elimOK (by decide) (by decide) cover1646 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1647 : P.CoversSplit 24 10 1647 0xcc000000000000000000000000000000cc0000000000000000320000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000cc0000000000000000320000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 572, 860, 872, 915, 1202, 1209, 1210, 1251, 1258]) (by decide +kernel)

theorem h1647 : P.leaf 34 1647 = 796572 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1647) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1647) (weight := fun _ => 1) (xs := [305, 308, 309, 378, 379, 382, 383, 506, 507, 510, 511, 817, 820, 821, 890, 891, 894, 895, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover1647 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1662 : P.CoversSplit 24 10 1662 0xcc00cc00880000000000000000000000c400c4000400000000310031000100000000000000000000003300330000000000000000000000000031003100000000cc00cc00880000000000000000000000c400c4000000000000310031000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 572, 860, 867, 915, 1202, 1209, 1217, 1258]) (by decide +kernel)

theorem c1662_0 : P.sumLeaves 24 1701888 1024 = 1754133 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1662) (lo := 0) (len := 1024) (W := 1754133) check rows elimOK (by decide) (by decide) cover1662 (by decide)
  decide +kernel

theorem h1662 : P.leaf 34 1662 = 1754133 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1754133)]) (.cons c1662_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(1485, 48), (1486, 48), (1487, 48), (1494, 24), (1495, 24), (1500, 48), (1501, 48), (1502, 48), (1503, 48), (1516, 24), (1517, 24), (1518, 48), (1519, 48), (1534, 24), (1535, 24), (1590, 24), (1591, 24), (1596, 24), (1597, 24), (1598, 24), (1599, 24), (1622, 8), (1623, 8), (1628, 24), (1629, 24), (1630, 24), (1631, 24), (1644, 24), (1645, 24), (1646, 48), (1647, 48), (1662, 24)]

theorem segOK : checkSeg 16 perms 1485 1663 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 1485 1663 1000 5165702064 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 5165702064)
    (SegSum.cons (w := 48) h1485 (SegSum.cons (w := 48) h1486 (SegSum.cons (w := 48) h1487 (SegSum.cons (w := 24) h1494 (SegSum.cons (w := 24) h1495 (SegSum.cons (w := 48) h1500 (SegSum.cons (w := 48) h1501 (SegSum.cons (w := 48) h1502 (SegSum.cons (w := 48) h1503 (SegSum.cons (w := 24) h1516 (SegSum.cons (w := 24) h1517 (SegSum.cons (w := 48) h1518 (SegSum.cons (w := 48) h1519 (SegSum.cons (w := 24) h1534 (SegSum.cons (w := 24) h1535 (SegSum.cons (w := 24) h1590 (SegSum.cons (w := 24) h1591 (SegSum.cons (w := 24) h1596 (SegSum.cons (w := 24) h1597 (SegSum.cons (w := 24) h1598 (SegSum.cons (w := 24) h1599 (SegSum.cons (w := 8) h1622 (SegSum.cons (w := 8) h1623 (SegSum.cons (w := 24) h1628 (SegSum.cons (w := 24) h1629 (SegSum.cons (w := 24) h1630 (SegSum.cons (w := 24) h1631 (SegSum.cons (w := 24) h1644 (SegSum.cons (w := 24) h1645 (SegSum.cons (w := 48) h1646 (SegSum.cons (w := 48) h1647 (SegSum.cons (w := 24) h1662 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S11
