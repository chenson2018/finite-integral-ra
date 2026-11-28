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

namespace RACert.S4N1.C0.S14

open RACert RACert.Problem

theorem cover2717 : P.CoversSplit 24 10 2717 0xaa000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 516, 517, 524, 528, 573, 859, 915, 916, 1210, 1251, 1259, 1264]) (ps := [(8, [615], [1266])]) (by decide +kernel)

theorem h2717 : P.leaf 34 2717 = 232256 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 2717) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 2717) (weight := fun _ => 1) (xs := [507, 511, 893, 895, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover2717 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1763 : P.leaf 34 1763 = 232256 :=
  orient4 (v := 2717) (by decide) (by decide +kernel) h2717

theorem cover2732 : P.CoversSplit 24 10 2732 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 517, 522, 524, 566, 573, 879, 915, 1258]) (by decide +kernel)

theorem h2732 : P.leaf 34 2732 = 13824 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 2732) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 2732) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover2732 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1764 : P.leaf 34 1764 = 13824 :=
  orient4 (v := 2732) (by decide) (by decide +kernel) h2732

theorem cover2733 : P.CoversSplit 24 10 2733 0xcc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 517, 522, 524, 566, 573, 879, 915, 1210]) (by decide +kernel)

theorem h2733 : P.leaf 34 2733 = 205568 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 2733) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 2733) (weight := fun _ => 1) (xs := [1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover2733 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1765 : P.leaf 34 1765 = 205568 :=
  orient4 (v := 2733) (by decide) (by decide +kernel) h2733

theorem cover1766 : P.CoversSplit 24 10 1766 0xaa000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 475, 515, 522, 524, 566, 573, 860, 915, 916, 921, 1209, 1258, 1259, 1308]) (by decide +kernel)

theorem h1766 : P.leaf 34 1766 = 244352 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1766) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1766) (weight := fun _ => 1) (xs := [507, 511, 893, 895, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover1766 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1767 : P.CoversSplit 24 10 1767 0xff000000000000000000000000000000ff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [475, 515, 522, 524, 566, 573, 860, 915, 916, 921, 1202, 1209, 1251, 1258, 1259, 1308]) (by decide +kernel)

theorem h1767 : P.leaf 34 1767 = 1589456 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1767) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1767) (weight := fun _ => 1) (xs := [506, 507, 510, 511, 888, 889, 890, 891, 892, 893, 894, 895, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover1767 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover2764 : P.CoversSplit 24 10 2764 0x8800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 516, 522, 536, 573, 859, 879, 915, 1258]) (ps := [(14, [929], [1266])]) (by decide +kernel)

theorem h2764 : P.leaf 34 2764 = 20336 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 2764) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 2764) (weight := fun _ => 1) (xs := [1019, 1023]) check rows elimOK (by decide) (by decide) cover2764 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1768 : P.leaf 34 1768 = 20336 :=
  orient4 (v := 2764) (by decide) (by decide +kernel) h2764

theorem cover2765 : P.CoversSplit 24 10 2765 0xcc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 516, 522, 536, 573, 859, 879, 915, 1210, 1251]) (ps := [(14, [929], [1266])]) (by decide +kernel)

theorem h2765 : P.leaf 34 2765 = 154624 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 2765) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 2765) (weight := fun _ => 1) (xs := [1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover2765 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1769 : P.leaf 34 1769 = 154624 :=
  orient4 (v := 2765) (by decide) (by decide +kernel) h2765

theorem cover1770 : P.CoversSplit 24 10 1770 0xaa000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 522, 523, 565, 573, 860, 872, 921, 1209, 1258, 1259, 1308]) (ps := [(14, [874], [860])]) (by decide +kernel)

theorem h1770 : P.leaf 34 1770 = 151720 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1770) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1770) (weight := fun _ => 1) (xs := [507, 511, 893, 895, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover1770 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover2781 : P.CoversSplit 24 10 2781 0xff000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 516, 536, 573, 859, 879, 908, 915, 916, 1210, 1251, 1259, 1264]) (ps := [(14, [929], [1266])]) (by decide +kernel)

theorem h2781 : P.leaf 34 2781 = 660032 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 2781) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 2781) (weight := fun _ => 1) (xs := [506, 507, 510, 511, 893, 895, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover2781 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1771 : P.leaf 34 1771 = 660032 :=
  orient4 (v := 2781) (by decide) (by decide +kernel) h2781

theorem cover1772 : P.CoversSplit 24 10 1772 0x8800000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 522, 573, 860, 872, 915, 1202, 1308]) (by decide +kernel)

theorem h1772 : P.leaf 34 1772 = 99880 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1772) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1772) (weight := fun _ => 1) (xs := [507, 511, 895, 1019, 1023]) check rows elimOK (by decide) (by decide) cover1772 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1773 : P.CoversSplit 24 10 1773 0xcc000000000000000000000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 573, 860, 872, 915, 1209, 1251, 1308, 1651]) (by decide +kernel)

theorem h1773 : P.leaf 34 1773 = 804576 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1773) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1773) (weight := fun _ => 1) (xs := [506, 507, 510, 511, 890, 891, 894, 895, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover1773 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1774 : P.CoversSplit 24 10 1774 0xaa000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 522, 573, 860, 872, 916, 921, 1209, 1258, 1259, 1308]) (by decide +kernel)

theorem h1774 : P.leaf 34 1774 = 856696 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1774) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1774) (weight := fun _ => 1) (xs := [507, 511, 893, 895, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover1774 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1775 : P.CoversSplit 24 10 1775 0xff000000000000000000000000000000ff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 573, 860, 916, 921, 1202, 1209, 1251, 1258, 1259, 1308]) (by decide +kernel)

theorem h1775 : P.leaf 34 1775 = 3133624 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1775) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1775) (weight := fun _ => 1) (xs := [506, 507, 510, 511, 888, 889, 890, 891, 892, 893, 894, 895, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover1775 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover2719 : P.CoversSplit 24 10 2719 0xaa000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 517, 524, 528, 573, 859, 916, 921, 1210, 1251, 1259, 1264]) (ps := [(8, [615], [1266])]) (by decide +kernel)

theorem h2719 : P.leaf 34 2719 = 645408 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 2719) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 2719) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 2719) (weight := rowWeight keep5 twice5) (xs := [507, 511, 893, 895, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover2719 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1779 : P.leaf 34 1779 = 645408 :=
  orient4 (v := 2719) (by decide) (by decide +kernel) h2719

theorem cover2734 : P.CoversSplit 24 10 2734 0xa0000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 517, 522, 524, 573, 859, 916, 921, 1202, 1209, 1210, 1258]) (by decide +kernel)

theorem h2734 : P.leaf 34 2734 = 210400 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 2734) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 2734) (weight := fun _ => 1) (xs := [893, 895, 1021, 1023]) check rows elimOK (by decide) (by decide) cover2734 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1780 : P.leaf 34 1780 = 210400 :=
  orient4 (v := 2734) (by decide) (by decide +kernel) h2734

theorem cover2735 : P.CoversSplit 24 10 2735 0xff000000000000000000000000000000ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 524, 573, 916, 921, 1202, 1210, 1251, 1258]) (by decide +kernel)

theorem h2735 : P.leaf 34 2735 = 1491880 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 2735) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 2735) (weight := fun _ => 1) (xs := [888, 889, 890, 891, 892, 893, 894, 895, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover2735 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1781 : P.leaf 34 1781 = 1491880 :=
  orient4 (v := 2735) (by decide) (by decide +kernel) h2735

theorem cover2750 : P.CoversSplit 24 10 2750 0xff00ff00a00000000000000000000000a500a5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 517, 524, 573, 859, 916, 921, 1202, 1210, 1217, 1259, 1264, 1308]) (by decide +kernel)

theorem c2750_0 : P.sumLeaves 24 2816000 1024 = 1634200 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 2750) (lo := 0) (len := 1024) (W := 1634200) check rows elimOK (by decide) (by decide) cover2750 (by decide)
  decide +kernel

theorem h2750 : P.leaf 34 2750 = 1634200 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1634200)]) (.cons c2750_0 (.nil)) (by decide) (by decide))

theorem h1782 : P.leaf 34 1782 = 1634200 :=
  orient4 (v := 2750) (by decide) (by decide +kernel) h2750

theorem cover2751 : P.CoversSplit 24 10 2751 0xff00ff00a00000000000000000000000ff00ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 524, 573, 916, 921, 1202, 1210, 1217, 1259, 1264, 1308]) (by decide +kernel)

theorem c2751_0 : P.sumLeaves 24 2817024 1024 = 5587628 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 2751) (lo := 0) (len := 1024) (W := 5587628) check rows elimOK (by decide) (by decide) cover2751 (by decide)
  decide +kernel

theorem h2751 : P.leaf 34 2751 = 5587628 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5587628)]) (.cons c2751_0 (.nil)) (by decide) (by decide))

theorem h1783 : P.leaf 34 1783 = 5587628 :=
  orient4 (v := 2751) (by decide) (by decide +kernel) h2751

theorem cover2766 : P.CoversSplit 24 10 2766 0xaa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 516, 522, 536, 573, 859, 879, 915, 916, 921, 1258]) (ps := [(14, [965], [1266])]) (by decide +kernel)

theorem h2766 : P.leaf 34 2766 = 162576 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 2766) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 2766) (weight := fun _ => 1) (xs := [1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover2766 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1784 : P.leaf 34 1784 = 162576 :=
  orient4 (v := 2766) (by decide) (by decide +kernel) h2766

theorem cover2767 : P.CoversSplit 24 10 2767 0xff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 516, 522, 536, 573, 859, 879, 915, 916, 921, 1210, 1251, 1258]) (ps := [(14, [965], [1266])]) (by decide +kernel)

theorem h2767 : P.leaf 34 2767 = 1069824 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 2767) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 2767) (weight := fun _ => 1) (xs := [1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover2767 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1785 : P.leaf 34 1785 = 1069824 :=
  orient4 (v := 2767) (by decide) (by decide +kernel) h2767

theorem cover2782 : P.CoversSplit 24 10 2782 0xff000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 516, 536, 573, 859, 879, 915, 916, 921, 1210, 1251, 1259, 1264]) (ps := [(14, [965], [1266])]) (by decide +kernel)

theorem h2782 : P.leaf 34 2782 = 919816 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 2782) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 2782) (weight := fun _ => 1) (xs := [506, 507, 510, 511, 893, 895, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover2782 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1786 : P.leaf 34 1786 = 919816 :=
  orient4 (v := 2782) (by decide) (by decide +kernel) h2782

theorem cover2783 : P.CoversSplit 24 10 2783 0xff000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 536, 573, 859, 879, 908, 915, 916, 921, 1210, 1251, 1259, 1264]) (ps := [(14, [965], [1266])]) (by decide +kernel)

theorem h2783 : P.leaf 34 2783 = 1927872 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 2783) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 2783) (weight := fun _ => 1) (xs := [506, 507, 510, 511, 893, 895, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover2783 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1787 : P.leaf 34 1787 = 1927872 :=
  orient4 (v := 2783) (by decide) (by decide +kernel) h2783

theorem cover2798 : P.CoversSplit 24 10 2798 0xaa000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 522, 573, 859, 879, 915, 916, 921, 1210, 1251, 1258, 1308]) (by decide +kernel)

theorem h2798 : P.leaf 34 2798 = 874408 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 2798) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 2798) (weight := fun _ => 1) (xs := [507, 511, 893, 895, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover2798 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1788 : P.leaf 34 1788 = 874408 :=
  orient4 (v := 2798) (by decide) (by decide +kernel) h2798

theorem cover2799 : P.CoversSplit 24 10 2799 0xff000000000000000000000000000000ff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 573, 859, 879, 915, 916, 921, 1202, 1210, 1251, 1258, 1308]) (by decide +kernel)

theorem h2799 : P.leaf 34 2799 = 3152344 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 2799) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 2799) (weight := fun _ => 1) (xs := [506, 507, 510, 511, 888, 889, 890, 891, 892, 893, 894, 895, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover2799 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1789 : P.leaf 34 1789 = 3152344 :=
  orient4 (v := 2799) (by decide) (by decide +kernel) h2799

theorem cover1790 : P.CoversSplit 24 10 1790 0xff00ff00aa0000000000000000000000f500f5000500000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 573, 860, 867, 916, 921, 1202, 1210, 1217, 1259, 1308]) (by decide +kernel)

theorem c1790_0 : P.sumLeaves 24 1832960 1024 = 5682202 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1790) (lo := 0) (len := 1024) (W := 5682202) check rows elimOK (by decide) (by decide) cover1790 (by decide)
  decide +kernel

theorem h1790 : P.leaf 34 1790 = 5682202 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5682202)]) (.cons c1790_0 (.nil)) (by decide) (by decide))

theorem cover1791 : P.CoversSplit 24 10 1791 0xff00ff00aa0000000000000000000000ff00ff00aa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [573, 860, 867, 916, 921, 1202, 1210, 1259, 1308]) (by decide +kernel)

theorem c1791_0 : P.sumLeaves 24 1833984 1024 = 11970716 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1791) (lo := 0) (len := 1024) (W := 11970716) check rows elimOK (by decide) (by decide) cover1791 (by decide)
  decide +kernel

theorem h1791 : P.leaf 34 1791 = 11970716 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 11970716)]) (.cons c1791_0 (.nil)) (by decide) (by decide))

theorem cover16924 : P.CoversSplit 24 10 16924 0x8000800000000000800080000000000080000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000080008000000000000000000000000000800080000000000080008000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 466, 472, 473, 516, 523, 524, 528, 573, 578, 859, 916, 1210, 1259]) (by decide +kernel)

theorem h16924 : P.leaf 34 16924 = 6450 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 16924) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 16924) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 16924) (weight := rowWeight keep1 twice1) (xs := [303, 319, 367, 383, 495, 511, 831, 895, 943, 959, 1007, 1023]) check rows elimOK (by decide) (by decide) cover16924 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1921 : P.leaf 34 1921 = 6450 :=
  orient24 (v := 16924) (by decide) (by decide +kernel) h16924

theorem cover16925 : P.CoversSplit 24 10 16925 0x8000800000000000800080000000000080000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000080008000000000000000000000000000800080000000000080008000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 516, 517, 523, 524, 528, 573, 578, 859, 916, 1210, 1259]) (by decide +kernel)

theorem h16925 : P.leaf 34 16925 = 101912 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 16925) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 16925) (weight := fun _ => 1) (xs := [303, 319, 367, 383, 495, 511, 831, 895, 943, 959, 1007, 1023]) check rows elimOK (by decide) (by decide) cover16925 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1923 : P.leaf 34 1923 = 101912 :=
  orient24 (v := 16925) (by decide) (by decide +kernel) h16925

theorem cover1924 : P.CoversSplit 24 10 1924 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 468, 473, 475, 479, 515, 516, 522, 566, 872, 915]) (by decide +kernel)

theorem h1924 : P.leaf 34 1924 = 3584 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1924) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1924) (weight := fun _ => 1) (xs := [511, 1023]) check rows elimOK (by decide) (by decide) cover1924 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1925 : P.CoversSplit 24 10 1925 0x8800000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [468, 473, 475, 515, 517, 522, 528, 566, 860, 915, 916, 1209, 1609]) (ps := [(14, [923], [1266])]) (by decide +kernel)

theorem h1925 : P.leaf 34 1925 = 28112 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1925) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1925) (weight := fun _ => 1) (xs := [507, 511, 895, 1019, 1023]) check rows elimOK (by decide) (by decide) cover1925 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3363 : P.CoversSplit 24 10 3363 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 517, 522, 524, 529, 565, 858, 865, 915, 1209]) (by decide +kernel)

theorem h3363 : P.leaf 34 3363 = 58336 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3363) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3363) (weight := fun _ => 1) (xs := [895, 1023]) check rows elimOK (by decide) (by decide) cover3363 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1926 : P.leaf 34 1926 = 58336 :=
  orient25 (v := 3363) (by decide) (by decide +kernel) h3363

theorem cover1927 : P.CoversSplit 24 10 1927 0xaaaa0000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000aaaa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [468, 515, 517, 522, 528, 566, 860, 915, 916, 1209, 1258, 1259]) (ps := [(3, [502], [524]), (14, [965], [1266])]) (by decide +kernel)

theorem h1927 : P.leaf 34 1927 = 510272 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1927) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1927) (weight := fun _ => 1) (xs := [497, 499, 501, 503, 505, 507, 509, 511, 885, 887, 893, 895, 1009, 1011, 1013, 1015, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover1927 (by decide) (by decide) (by decide +kernel)
  decide +kernel

def seg : List (ℕ × ℕ) := [(1763, 48), (1764, 48), (1765, 48), (1766, 48), (1767, 48), (1768, 48), (1769, 48), (1770, 48), (1771, 48), (1772, 48), (1773, 48), (1774, 48), (1775, 48), (1779, 24), (1780, 48), (1781, 48), (1782, 48), (1783, 48), (1784, 48), (1785, 48), (1786, 48), (1787, 48), (1788, 48), (1789, 48), (1790, 48), (1791, 48), (1921, 12), (1923, 24), (1924, 48), (1925, 48), (1926, 48), (1927, 48)]

theorem segOK : checkSeg 16 perms 1763 1928 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 1763 1928 1452 2103666552 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 2103666552)
    (SegSum.cons (w := 48) h1763 (SegSum.cons (w := 48) h1764 (SegSum.cons (w := 48) h1765 (SegSum.cons (w := 48) h1766 (SegSum.cons (w := 48) h1767 (SegSum.cons (w := 48) h1768 (SegSum.cons (w := 48) h1769 (SegSum.cons (w := 48) h1770 (SegSum.cons (w := 48) h1771 (SegSum.cons (w := 48) h1772 (SegSum.cons (w := 48) h1773 (SegSum.cons (w := 48) h1774 (SegSum.cons (w := 48) h1775 (SegSum.cons (w := 24) h1779 (SegSum.cons (w := 48) h1780 (SegSum.cons (w := 48) h1781 (SegSum.cons (w := 48) h1782 (SegSum.cons (w := 48) h1783 (SegSum.cons (w := 48) h1784 (SegSum.cons (w := 48) h1785 (SegSum.cons (w := 48) h1786 (SegSum.cons (w := 48) h1787 (SegSum.cons (w := 48) h1788 (SegSum.cons (w := 48) h1789 (SegSum.cons (w := 48) h1790 (SegSum.cons (w := 48) h1791 (SegSum.cons (w := 12) h1921 (SegSum.cons (w := 24) h1923 (SegSum.cons (w := 48) h1924 (SegSum.cons (w := 48) h1925 (SegSum.cons (w := 48) h1926 (SegSum.cons (w := 48) h1927 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S14
