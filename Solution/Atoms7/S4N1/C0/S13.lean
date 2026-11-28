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

namespace RACert.S4N1.C0.S13

open RACert RACert.Problem

theorem cover2790 : P.CoversSplit 24 10 2790 0xaa000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 475, 515, 522, 524, 566, 573, 859, 915, 916, 921, 1210, 1258, 1308]) (ps := [(14, [880], [859])]) (by decide +kernel)

theorem h2790 : P.leaf 34 2790 = 114816 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 2790) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 2790) (weight := fun _ => 1) (xs := [507, 511, 893, 895, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover2790 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1724 : P.leaf 34 1724 = 114816 :=
  orient4 (v := 2790) (by decide) (by decide +kernel) h2790

theorem cover1725 : P.CoversSplit 24 10 1725 0xff000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 517, 524, 566, 573, 860, 872, 915, 1209, 1251, 1258, 1259, 1264, 1308]) (ps := [(8, [531], [517])]) (by decide +kernel)

theorem h1725 : P.leaf 34 1725 = 682624 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1725) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1725) (weight := fun _ => 1) (xs := [506, 507, 510, 511, 893, 895, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover1725 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1726 : P.CoversSplit 24 10 1726 0xff000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 517, 524, 566, 573, 860, 872, 916, 921, 1209, 1251, 1259, 1308]) (ps := [(8, [531], [517])]) (by decide +kernel)

theorem h1726 : P.leaf 34 1726 = 798160 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1726) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1726) (weight := fun _ => 1) (xs := [506, 507, 510, 511, 893, 895, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover1726 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1727 : P.CoversSplit 24 10 1727 0xff000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 524, 566, 573, 860, 872, 916, 921, 1209, 1251, 1259, 1308]) (ps := [(8, [531], [517])]) (by decide +kernel)

theorem h1727 : P.leaf 34 1727 = 2014576 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1727) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1727) (weight := fun _ => 1) (xs := [506, 507, 510, 511, 893, 895, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover1727 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover2712 : P.CoversSplit 24 10 2712 0xaa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 467, 473, 474, 486, 487, 516, 517, 524, 879, 1210, 1259]) (by decide +kernel)

theorem h2712 : P.leaf 34 2712 = 5376 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 2712) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 2712) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 2712) (weight := rowWeight keep5 twice5) (xs := [1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover2712 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1730 : P.leaf 34 1730 = 5376 :=
  orient4 (v := 2712) (by decide) (by decide +kernel) h2712

theorem cover2713 : P.CoversSplit 24 10 2713 0xaa000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [467, 473, 474, 487, 516, 517, 524, 528, 859, 1210, 1259, 1264]) (by decide +kernel)

theorem h2713 : P.leaf 34 2713 = 89568 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 2713) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 2713) (weight := fun _ => 1) (xs := [893, 895, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover2713 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1731 : P.leaf 34 1731 = 89568 :=
  orient4 (v := 2713) (by decide) (by decide +kernel) h2713

theorem cover1732 : P.CoversSplit 24 10 1732 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 475, 508, 515, 516, 522, 536, 566, 573, 860, 872, 915, 916]) (by decide +kernel)

theorem h1732 : P.leaf 34 1732 = 2336 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1732) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1732) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover1732 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1733 : P.CoversSplit 24 10 1733 0xcc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 475, 515, 522, 536, 566, 573, 860, 872, 915, 916]) (by decide +kernel)

theorem h1733 : P.leaf 34 1733 = 47904 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1733) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1733) (weight := fun _ => 1) (xs := [1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover1733 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1734 : P.CoversSplit 24 10 1734 0xa0000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 475, 515, 516, 522, 536, 566, 860, 915, 916, 921, 1209, 1210, 1258, 1259]) (by decide +kernel)

theorem h1734 : P.leaf 34 1734 = 49568 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1734) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1734) (weight := fun _ => 1) (xs := [893, 895, 1021, 1023]) check rows elimOK (by decide) (by decide) cover1734 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1735 : P.CoversSplit 24 10 1735 0xff000000000000000000000000000000ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [475, 515, 522, 536, 566, 573, 860, 915, 916, 921, 1202, 1209, 1258, 1259]) (by decide +kernel)

theorem h1735 : P.leaf 34 1735 = 938160 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1735) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1735) (weight := fun _ => 1) (xs := [888, 889, 890, 891, 892, 893, 894, 895, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover1735 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1736 : P.CoversSplit 24 10 1736 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 474, 508, 515, 516, 522, 523, 536, 573, 860, 872, 915, 1202, 1210]) (ps := [(14, [509], [487])]) (by decide +kernel)

theorem h1736 : P.leaf 34 1736 = 3824 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1736) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1736) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover1736 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1737 : P.CoversSplit 24 10 1737 0xcc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 474, 515, 522, 536, 573, 860, 872, 915, 1209, 1251, 1651]) (ps := [(14, [929], [487])]) (by decide +kernel)

theorem h1737 : P.leaf 34 1737 = 30768 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1737) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1737) (weight := fun _ => 1) (xs := [1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover1737 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1738 : P.CoversSplit 24 10 1738 0xa0000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 516, 522, 523, 536, 860, 921, 1202, 1209, 1210]) (by decide +kernel)

theorem h1738 : P.leaf 34 1738 = 20312 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1738) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1738) (weight := fun _ => 1) (xs := [893, 895, 1021, 1023]) check rows elimOK (by decide) (by decide) cover1738 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover2777 : P.CoversSplit 24 10 2777 0xff000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [467, 473, 474, 487, 516, 859, 879, 915, 916, 1210, 1259, 1264]) (by decide +kernel)

theorem h2777 : P.leaf 34 2777 = 254208 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 2777) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 2777) (weight := fun _ => 1) (xs := [893, 895, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover2777 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1739 : P.leaf 34 1739 = 254208 :=
  orient4 (v := 2777) (by decide) (by decide +kernel) h2777

theorem cover1740 : P.CoversSplit 24 10 1740 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 516, 522, 536, 573, 860, 872, 915, 1210]) (ps := [(14, [929], [1266])]) (by decide +kernel)

theorem h1740 : P.leaf 34 1740 = 14160 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1740) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1740) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover1740 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1741 : P.CoversSplit 24 10 1741 0xcc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 522, 536, 573, 860, 872, 915, 1209, 1251, 1651]) (ps := [(14, [929], [1266])]) (by decide +kernel)

theorem h1741 : P.leaf 34 1741 = 169600 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1741) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1741) (weight := fun _ => 1) (xs := [1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover1741 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1742 : P.CoversSplit 24 10 1742 0xa0000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 516, 522, 536, 860, 916, 921, 1202, 1209, 1210, 1258, 1259]) (by decide +kernel)

theorem h1742 : P.leaf 34 1742 = 181952 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1742) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1742) (weight := fun _ => 1) (xs := [893, 895, 1021, 1023]) check rows elimOK (by decide) (by decide) cover1742 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1743 : P.CoversSplit 24 10 1743 0xff000000000000000000000000000000ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 536, 860, 916, 921, 1202, 1209, 1258, 1259]) (by decide +kernel)

theorem h1743 : P.leaf 34 1743 = 1686904 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1743) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1743) (weight := fun _ => 1) (xs := [888, 889, 890, 891, 892, 893, 894, 895, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover1743 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover2715 : P.CoversSplit 24 10 2715 0xaa000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [467, 487, 516, 517, 524, 528, 573, 859, 916, 921, 1210, 1251, 1259, 1264]) (by decide +kernel)

theorem h2715 : P.leaf 34 2715 = 309216 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 2715) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 2715) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 2715) (weight := rowWeight keep5 twice5) (xs := [383, 507, 511, 893, 895, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover2715 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1747 : P.leaf 34 1747 = 309216 :=
  orient4 (v := 2715) (by decide) (by decide +kernel) h2715

theorem cover2730 : P.CoversSplit 24 10 2730 0xa0000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 517, 522, 524, 573, 859, 916, 921, 1202, 1209, 1210, 1258]) (by decide +kernel)

theorem h2730 : P.leaf 34 2730 = 53776 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 2730) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 2730) (weight := fun _ => 1) (xs := [893, 895, 1021, 1023]) check rows elimOK (by decide) (by decide) cover2730 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1748 : P.leaf 34 1748 = 53776 :=
  orient4 (v := 2730) (by decide) (by decide +kernel) h2730

theorem cover2731 : P.CoversSplit 24 10 2731 0xff000000000000000000000000000000ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 524, 573, 916, 921, 1202, 1210, 1251, 1258]) (by decide +kernel)

theorem h2731 : P.leaf 34 2731 = 897488 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 2731) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 2731) (weight := fun _ => 1) (xs := [888, 889, 890, 891, 892, 893, 894, 895, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover2731 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1749 : P.leaf 34 1749 = 897488 :=
  orient4 (v := 2731) (by decide) (by decide +kernel) h2731

theorem cover1750 : P.CoversSplit 24 10 1750 0xff00ff00a00000000000000000000000a000a5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 475, 516, 573, 860, 915, 916, 921, 1202, 1210, 1259]) (ps := [(14, [965], [860, 1266])]) (by decide +kernel)

theorem c1750_0 : P.sumLeaves 24 1792000 1024 = 699716 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1750) (lo := 0) (len := 1024) (W := 699716) check rows elimOK (by decide) (by decide) cover1750 (by decide)
  decide +kernel

theorem h1750 : P.leaf 34 1750 = 699716 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 699716)]) (.cons c1750_0 (.nil)) (by decide) (by decide))

theorem cover1751 : P.CoversSplit 24 10 1751 0xff00ff00a00000000000000000000000ff00ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [475, 516, 573, 860, 915, 916, 921, 1202, 1210, 1217, 1259]) (ps := [(14, [965], [1217, 1266])]) (by decide +kernel)

theorem c1751_0 : P.sumLeaves 24 1793024 1024 = 3382360 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1751) (lo := 0) (len := 1024) (W := 3382360) check rows elimOK (by decide) (by decide) cover1751 (by decide)
  decide +kernel

theorem h1751 : P.leaf 34 1751 = 3382360 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3382360)]) (.cons c1751_0 (.nil)) (by decide) (by decide))

theorem cover2762 : P.CoversSplit 24 10 2762 0xaa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 467, 515, 522, 523, 536, 859, 879, 915, 916]) (by decide +kernel)

theorem h2762 : P.leaf 34 2762 = 76280 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 2762) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 2762) (weight := fun _ => 1) (xs := [1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover2762 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1752 : P.leaf 34 1752 = 76280 :=
  orient4 (v := 2762) (by decide) (by decide +kernel) h2762

theorem cover2763 : P.CoversSplit 24 10 2763 0xff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [467, 515, 516, 522, 523, 536, 573, 859, 879, 915, 916, 921, 1210, 1251, 1258]) (ps := [(14, [1272], [1266])]) (by decide +kernel)

theorem h2763 : P.leaf 34 2763 = 444104 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 2763) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 2763) (weight := fun _ => 1) (xs := [1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover2763 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1753 : P.leaf 34 1753 = 444104 :=
  orient4 (v := 2763) (by decide) (by decide +kernel) h2763

theorem cover2778 : P.CoversSplit 24 10 2778 0xff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 467, 487, 516, 573, 859, 879, 915, 916, 921, 1210, 1251, 1259]) (by decide +kernel)

theorem h2778 : P.leaf 34 2778 = 361836 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 2778) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 2778) (weight := fun _ => 1) (xs := [506, 507, 510, 511, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover2778 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1754 : P.leaf 34 1754 = 361836 :=
  orient4 (v := 2778) (by decide) (by decide +kernel) h2778

theorem cover2779 : P.CoversSplit 24 10 2779 0xff000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [467, 487, 516, 573, 859, 879, 915, 916, 921, 1210, 1251, 1259, 1264]) (by decide +kernel)

theorem h2779 : P.leaf 34 2779 = 987288 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 2779) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 2779) (weight := fun _ => 1) (xs := [383, 506, 507, 510, 511, 893, 895, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover2779 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1755 : P.leaf 34 1755 = 987288 :=
  orient4 (v := 2779) (by decide) (by decide +kernel) h2779

theorem cover2794 : P.CoversSplit 24 10 2794 0xaa000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 522, 523, 573, 859, 879, 915, 916, 921, 1210, 1251, 1258, 1308]) (by decide +kernel)

theorem h2794 : P.leaf 34 2794 = 362944 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 2794) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 2794) (weight := fun _ => 1) (xs := [507, 511, 893, 895, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover2794 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1756 : P.leaf 34 1756 = 362944 :=
  orient4 (v := 2794) (by decide) (by decide +kernel) h2794

theorem cover2795 : P.CoversSplit 24 10 2795 0xff000000000000000000000000000000ff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 523, 573, 859, 879, 915, 916, 921, 1202, 1210, 1251, 1258, 1308]) (by decide +kernel)

theorem h2795 : P.leaf 34 2795 = 1650264 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 2795) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 2795) (weight := fun _ => 1) (xs := [506, 507, 510, 511, 888, 889, 890, 891, 892, 893, 894, 895, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover2795 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1757 : P.leaf 34 1757 = 1650264 :=
  orient4 (v := 2795) (by decide) (by decide +kernel) h2795

theorem cover1758 : P.CoversSplit 24 10 1758 0xff00ff00a00000000000000000000000a000a5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 516, 536, 573, 860, 916, 921, 1202, 1210, 1259]) (ps := [(14, [965], [860, 1266])]) (by decide +kernel)

theorem c1758_0 : P.sumLeaves 24 1800192 1024 = 2224200 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1758) (lo := 0) (len := 1024) (W := 2224200) check rows elimOK (by decide) (by decide) cover1758 (by decide)
  decide +kernel

theorem h1758 : P.leaf 34 1758 = 2224200 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2224200)]) (.cons c1758_0 (.nil)) (by decide) (by decide))

theorem cover1759 : P.CoversSplit 24 10 1759 0xff00ff00a00000000000000000000000ff00ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 536, 573, 860, 916, 921, 1202, 1210, 1217, 1259]) (ps := [(14, [965], [1217, 1266])]) (by decide +kernel)

theorem c1759_0 : P.sumLeaves 24 1801216 1024 = 5767988 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1759) (lo := 0) (len := 1024) (W := 5767988) check rows elimOK (by decide) (by decide) cover1759 (by decide)
  decide +kernel

theorem h1759 : P.leaf 34 1759 = 5767988 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5767988)]) (.cons c1759_0 (.nil)) (by decide) (by decide))

theorem cover2716 : P.CoversSplit 24 10 2716 0xaa000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 516, 524, 536, 573, 859, 879, 915, 916, 1210, 1251, 1259, 1264]) (ps := [(8, [531], [1266])]) (by decide +kernel)

theorem h2716 : P.leaf 34 2716 = 15472 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 2716) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 2716) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 2716) (weight := rowWeight keep5 twice5) (xs := [507, 511, 893, 895, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover2716 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1762 : P.leaf 34 1762 = 15472 :=
  orient4 (v := 2716) (by decide) (by decide +kernel) h2716

def seg : List (ℕ × ℕ) := [(1724, 48), (1725, 48), (1726, 48), (1727, 48), (1730, 24), (1731, 48), (1732, 48), (1733, 48), (1734, 48), (1735, 48), (1736, 48), (1737, 48), (1738, 48), (1739, 48), (1740, 48), (1741, 48), (1742, 48), (1743, 48), (1747, 24), (1748, 48), (1749, 48), (1750, 48), (1751, 48), (1752, 48), (1753, 48), (1754, 48), (1755, 48), (1756, 48), (1757, 48), (1758, 48), (1759, 48), (1762, 24)]

theorem segOK : checkSeg 16 perms 1724 1763 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 1724 1763 1464 1160290368 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1160290368)
    (SegSum.cons (w := 48) h1724 (SegSum.cons (w := 48) h1725 (SegSum.cons (w := 48) h1726 (SegSum.cons (w := 48) h1727 (SegSum.cons (w := 24) h1730 (SegSum.cons (w := 48) h1731 (SegSum.cons (w := 48) h1732 (SegSum.cons (w := 48) h1733 (SegSum.cons (w := 48) h1734 (SegSum.cons (w := 48) h1735 (SegSum.cons (w := 48) h1736 (SegSum.cons (w := 48) h1737 (SegSum.cons (w := 48) h1738 (SegSum.cons (w := 48) h1739 (SegSum.cons (w := 48) h1740 (SegSum.cons (w := 48) h1741 (SegSum.cons (w := 48) h1742 (SegSum.cons (w := 48) h1743 (SegSum.cons (w := 24) h1747 (SegSum.cons (w := 48) h1748 (SegSum.cons (w := 48) h1749 (SegSum.cons (w := 48) h1750 (SegSum.cons (w := 48) h1751 (SegSum.cons (w := 48) h1752 (SegSum.cons (w := 48) h1753 (SegSum.cons (w := 48) h1754 (SegSum.cons (w := 48) h1755 (SegSum.cons (w := 48) h1756 (SegSum.cons (w := 48) h1757 (SegSum.cons (w := 48) h1758 (SegSum.cons (w := 48) h1759 (SegSum.cons (w := 24) h1762 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S13
