/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S6N0.C0.Defs

/-! Generated certificate for the identity on six symmetric diversity atoms. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S6N0.C0.S47

open RACert RACert.Problem

theorem cover78687 : P.CoversSplit 26 10 78687 0xaaaa0000aaaa00000000000000000000aaa80000aaa8000000000000000000000000000000000000050500000505000000000000000000000504000005000000aaaa0000aaaa00000000000000000000aa8800000000000000000000000000000000000000000000050500000505000000000000000000000504000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 579, 930, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c78687_0 : P.sumLeaves 26 80575488 1024 = 10205170 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78687) (lo := 0) (len := 1024) (W := 10205170) check rows elimOK (by decide) (by decide) cover78687 (by decide)
  decide +kernel

theorem h78687 : P.leaf 36 78687 = 10205170 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 10205170)]) (.cons c78687_0 (.nil)) (by decide) (by decide))

theorem cover78718 : P.CoversSplit 26 10 78718 0xfffffffafffffafa000000000000000000000000000000000000000000000000555550505555505055555050555550500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 867, 873, 874, 972, 1315, 1658]) (by decide +kernel)

theorem c78718_0 : P.sumLeaves 26 80607232 1014 = 4040626 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78718) (lo := 0) (len := 1014) (W := 4040626) check rows elimOK (by decide) (by decide) cover78718 (by decide)
  decide +kernel

theorem c78718_1 : P.sumLeaves 26 80608246 10 = 1458834 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78718) (lo := 1014) (len := 10) (W := 1458834) check rows elimOK (by decide) (by decide) cover78718 (by decide)
  decide +kernel

theorem h78718 : P.leaf 36 78718 = 5499460 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1014, 4040626), (10, 1458834)]) (.cons c78718_0 (.cons c78718_1 (.nil))) (by decide) (by decide))

theorem cover78719 : P.CoversSplit 26 10 78719 0xfffffffafffffafa0000000000000000fffcfff8fffcc8c855545550550040005555505055555050555550505555505055545050555440405554505055004000fffffffafffffafa0000000000000000ffccffc8cc00c80055445540440040005555505055555050555550505555505055445040440040005544504044004000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 873, 930, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c78719_0 : P.sumLeaves 26 80608256 360 = 8952642 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78719) (lo := 0) (len := 360) (W := 8952642) check rows elimOK (by decide) (by decide) cover78719 (by decide)
  decide +kernel

theorem c78719_1 : P.sumLeaves 26 80608616 234 = 54674198 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78719) (lo := 360) (len := 234) (W := 54674198) check rows elimOK (by decide) (by decide) cover78719 (by decide)
  decide +kernel

theorem c78719_2 : P.sumLeaves 26 80608850 262 = 23820962 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78719) (lo := 594) (len := 262) (W := 23820962) check rows elimOK (by decide) (by decide) cover78719 (by decide)
  decide +kernel

theorem c78719_3 : P.sumLeaves 26 80609112 168 = 101220746 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78719) (lo := 856) (len := 168) (W := 101220746) check rows elimOK (by decide) (by decide) cover78719 (by decide)
  decide +kernel

theorem h78719 : P.leaf 36 78719 = 188668548 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(360, 8952642), (234, 54674198), (262, 23820962), (168, 101220746)]) (.cons c78719_0 (.cons c78719_1 (.cons c78719_2 (.cons c78719_3 (.nil))))) (by decide) (by decide))

theorem cover78727 : P.CoversSplit 26 10 78727 0xcc00000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 930, 972, 979, 1266, 1315, 1658, 1665]) (by decide +kernel)

theorem c78727_0 : P.sumLeaves 26 80616448 1024 = 83888 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78727) (lo := 0) (len := 1024) (W := 83888) check rows elimOK (by decide) (by decide) cover78727 (by decide)
  decide +kernel

theorem h78727 : P.leaf 36 78727 = 83888 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 83888)]) (.cons c78727_0 (.nil)) (by decide) (by decide))

theorem cover78729 : P.CoversSplit 26 10 78729 0xf0f0000000000000f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 538, 566, 923, 930, 972, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c78729_0 : P.sumLeaves 26 80618496 1024 = 16384 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78729) (lo := 0) (len := 1024) (W := 16384) check rows elimOK (by decide) (by decide) cover78729 (by decide)
  decide +kernel

theorem h78729 : P.leaf 36 78729 = 16384 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 16384)]) (.cons c78729_0 (.nil)) (by decide) (by decide))

theorem cover78731 : P.CoversSplit 26 10 78731 0xf0f0000000000000f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 538, 615, 930, 972, 979, 1266, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c78731_0 : P.sumLeaves 26 80620544 1024 = 89600 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78731) (lo := 0) (len := 1024) (W := 89600) check rows elimOK (by decide) (by decide) cover78731 (by decide)
  decide +kernel

theorem h78731 : P.leaf 36 78731 = 89600 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 89600)]) (.cons c78731_0 (.nil)) (by decide) (by decide))

theorem cover78734 : P.CoversSplit 26 10 78734 0xffff000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffcc0000cccc0808aa880000888808080000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 873, 930, 979, 1266, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c78734_0 : P.sumLeaves 26 80623616 1024 = 56606 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78734) (lo := 0) (len := 1024) (W := 56606) check rows elimOK (by decide) (by decide) cover78734 (by decide)
  decide +kernel

theorem h78734 : P.leaf 36 78734 = 56606 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 56606)]) (.cons c78734_0 (.nil)) (by decide) (by decide))

theorem cover78735 : P.CoversSplit 26 10 78735 0xffff000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffcc0000ffcc0a08aa880000aa880a080000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 930, 979, 1266, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c78735_0 : P.sumLeaves 26 80624640 1024 = 966304 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78735) (lo := 0) (len := 1024) (W := 966304) check rows elimOK (by decide) (by decide) cover78735 (by decide)
  decide +kernel

theorem h78735 : P.leaf 36 78735 = 966304 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 966304)]) (.cons c78735_0 (.nil)) (by decide) (by decide))

theorem cover78740 : P.CoversSplit 26 10 78740 0xcc00000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000333300003300000022220000220000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [467, 489, 538, 923, 930, 979, 1658, 1665]) (by decide +kernel)

theorem c78740_0 : P.sumLeaves 26 80629760 1024 = 35168 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78740) (lo := 0) (len := 1024) (W := 35168) check rows elimOK (by decide) (by decide) cover78740 (by decide)
  decide +kernel

theorem h78740 : P.leaf 36 78740 = 35168 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 35168)]) (.cons c78740_0 (.nil)) (by decide) (by decide))

theorem cover78741 : P.CoversSplit 26 10 78741 0xcc00000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 873, 923, 930, 972, 979, 1315, 1658, 1665]) (by decide +kernel)

theorem c78741_0 : P.sumLeaves 26 80630784 1024 = 50256 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78741) (lo := 0) (len := 1024) (W := 50256) check rows elimOK (by decide) (by decide) cover78741 (by decide)
  decide +kernel

theorem h78741 : P.leaf 36 78741 = 50256 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 50256)]) (.cons c78741_0 (.nil)) (by decide) (by decide))

theorem cover78742 : P.CoversSplit 26 10 78742 0xcc00000000000000cc00000000000000000000000000000000000000000000000c0000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000333300003300030022220000220002000000000000000000000000000000000003030000030000000202000002000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 873, 930, 972, 979, 1315, 1658, 1665]) (by decide +kernel)

theorem c78742_0 : P.sumLeaves 26 80631808 1024 = 172902 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78742) (lo := 0) (len := 1024) (W := 172902) check rows elimOK (by decide) (by decide) cover78742 (by decide)
  decide +kernel

theorem h78742 : P.leaf 36 78742 = 172902 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 172902)]) (.cons c78742_0 (.nil)) (by decide) (by decide))

theorem cover78743 : P.CoversSplit 26 10 78743 0xcc00000000000000cc00000000000000000000000000000000000000000000000c0000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 873, 930, 972, 979, 1315, 1658, 1665]) (by decide +kernel)

theorem c78743_0 : P.sumLeaves 26 80632832 1024 = 453508 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78743) (lo := 0) (len := 1024) (W := 453508) check rows elimOK (by decide) (by decide) cover78743 (by decide)
  decide +kernel

theorem h78743 : P.leaf 36 78743 = 453508 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 453508)]) (.cons c78743_0 (.nil)) (by decide) (by decide))

theorem cover78745 : P.CoversSplit 26 10 78745 0xf0f0000000000000f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 538, 615, 923, 930, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c78745_0 : P.sumLeaves 26 80634880 1024 = 108256 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78745) (lo := 0) (len := 1024) (W := 108256) check rows elimOK (by decide) (by decide) cover78745 (by decide)
  decide +kernel

theorem h78745 : P.leaf 36 78745 = 108256 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 108256)]) (.cons c78745_0 (.nil)) (by decide) (by decide))

theorem cover78747 : P.CoversSplit 26 10 78747 0xf0f0000000000000f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 538, 615, 873, 930, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c78747_0 : P.sumLeaves 26 80636928 1024 = 352640 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78747) (lo := 0) (len := 1024) (W := 352640) check rows elimOK (by decide) (by decide) cover78747 (by decide)
  decide +kernel

theorem h78747 : P.leaf 36 78747 = 352640 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 352640)]) (.cons c78747_0 (.nil)) (by decide) (by decide))

theorem cover78748 : P.CoversSplit 26 10 78748 0xffff000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [467, 538, 867, 923, 1273, 1322]) (by decide +kernel)

theorem c78748_0 : P.sumLeaves 26 80637952 1024 = 125312 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78748) (lo := 0) (len := 1024) (W := 125312) check rows elimOK (by decide) (by decide) cover78748 (by decide)
  decide +kernel

theorem h78748 : P.leaf 36 78748 = 125312 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 125312)]) (.cons c78748_0 (.nil)) (by decide) (by decide))

theorem cover78749 : P.CoversSplit 26 10 78749 0xffff000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000330000003300030022000000220002000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 873, 923, 930, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c78749_0 : P.sumLeaves 26 80638976 1024 = 418416 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78749) (lo := 0) (len := 1024) (W := 418416) check rows elimOK (by decide) (by decide) cover78749 (by decide)
  decide +kernel

theorem h78749 : P.leaf 36 78749 = 418416 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 418416)]) (.cons c78749_0 (.nil)) (by decide) (by decide))

theorem cover78750 : P.CoversSplit 26 10 78750 0xffff000000000000ffff000000000000000000000000000000000000000000000f0f0000000000000a0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 867, 873, 972, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c78750_0 : P.sumLeaves 26 80640000 1024 = 641480 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78750) (lo := 0) (len := 1024) (W := 641480) check rows elimOK (by decide) (by decide) cover78750 (by decide)
  decide +kernel

theorem h78750 : P.leaf 36 78750 = 641480 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 641480)]) (.cons c78750_0 (.nil)) (by decide) (by decide))

theorem cover78751 : P.CoversSplit 26 10 78751 0xffff000000000000ffff000000000000000000000000000000000000000000000f0f0a0a000000000a0a0a0a000000000000000000000000000000000000000000000000000000000000000000000000330000003300030022000000220002000000000000000000000000000000000003000200030002000200020002000200 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 873, 930, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c78751_0 : P.sumLeaves 26 80641024 1024 = 3286513 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78751) (lo := 0) (len := 1024) (W := 3286513) check rows elimOK (by decide) (by decide) cover78751 (by decide)
  decide +kernel

theorem h78751 : P.leaf 36 78751 = 3286513 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3286513)]) (.cons c78751_0 (.nil)) (by decide) (by decide))

theorem cover78774 : P.CoversSplit 26 10 78774 0xcc00cc0000000000cc00cc000000000000000000000000000000000000000000cc00c0000000000088008000000000000000000000000000000000000000000000000000000000000000000000000000333333303300300022222220220020000000000000000000000000000000000033333030330030002222202022002000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 873, 930, 972, 979, 1315, 1658, 1665]) (by decide +kernel)

theorem c78774_0 : P.sumLeaves 26 80664576 1024 = 932856 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78774) (lo := 0) (len := 1024) (W := 932856) check rows elimOK (by decide) (by decide) cover78774 (by decide)
  decide +kernel

theorem h78774 : P.leaf 36 78774 = 932856 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 932856)]) (.cons c78774_0 (.nil)) (by decide) (by decide))

theorem cover78775 : P.CoversSplit 26 10 78775 0xcc00cc0000000000cc00cc000000000000000000000000000000000000000000cc00c0000000000088008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 873, 930, 972, 979, 1658, 1665]) (by decide +kernel)

theorem c78775_0 : P.sumLeaves 26 80665600 1024 = 3683424 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78775) (lo := 0) (len := 1024) (W := 3683424) check rows elimOK (by decide) (by decide) cover78775 (by decide)
  decide +kernel

theorem h78775 : P.leaf 36 78775 = 3683424 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3683424)]) (.cons c78775_0 (.nil)) (by decide) (by decide))

theorem cover78776 : P.CoversSplit 26 10 78776 0xf0f0f0f500000000f0f0f0f50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 867, 873, 874, 923, 972, 1273]) (by decide +kernel)

theorem c78776_0 : P.sumLeaves 26 80666624 1024 = 102032 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78776) (lo := 0) (len := 1024) (W := 102032) check rows elimOK (by decide) (by decide) cover78776 (by decide)
  decide +kernel

theorem h78776 : P.leaf 36 78776 = 102032 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 102032)]) (.cons c78776_0 (.nil)) (by decide) (by decide))

theorem cover78777 : P.CoversSplit 26 10 78777 0xf0f0f0f500000000f0f0f0f50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300030003000300020002000200020000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 923, 930, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c78777_0 : P.sumLeaves 26 80667648 1024 = 1079392 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78777) (lo := 0) (len := 1024) (W := 1079392) check rows elimOK (by decide) (by decide) cover78777 (by decide)
  decide +kernel

theorem h78777 : P.leaf 36 78777 = 1079392 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1079392)]) (.cons c78777_0 (.nil)) (by decide) (by decide))

theorem cover78778 : P.CoversSplit 26 10 78778 0xf0f0f0f500000000f0f0f0f50000000000000000000000000000000000000000000050500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 867, 873, 874, 972, 1273, 1658]) (by decide +kernel)

theorem c78778_0 : P.sumLeaves 26 80668672 1024 = 703914 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78778) (lo := 0) (len := 1024) (W := 703914) check rows elimOK (by decide) (by decide) cover78778 (by decide)
  decide +kernel

theorem h78778 : P.leaf 36 78778 = 703914 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 703914)]) (.cons c78778_0 (.nil)) (by decide) (by decide))

theorem cover78779 : P.CoversSplit 26 10 78779 0xf0f0f0f500000000f0f0f0f50000000000000000000000000000000000000000000050500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300030003000300020002000200020000000000000000000000000000000000000001000000010000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 873, 930, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c78779_0 : P.sumLeaves 26 80669696 1024 = 3267486 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78779) (lo := 0) (len := 1024) (W := 3267486) check rows elimOK (by decide) (by decide) cover78779 (by decide)
  decide +kernel

theorem h78779 : P.leaf 36 78779 = 3267486 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3267486)]) (.cons c78779_0 (.nil)) (by decide) (by decide))

theorem cover78782 : P.CoversSplit 26 10 78782 0xfffffffa00000000fffffffa0000000000000000000000000000000000000000fffff0f000000000aaaaa0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 867, 873, 874, 972, 1273, 1658]) (by decide +kernel)

theorem c78782_0 : P.sumLeaves 26 80672768 1024 = 4236932 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78782) (lo := 0) (len := 1024) (W := 4236932) check rows elimOK (by decide) (by decide) cover78782 (by decide)
  decide +kernel

theorem h78782 : P.leaf 36 78782 = 4236932 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4236932)]) (.cons c78782_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(78687, 720), (78718, 180), (78719, 180), (78727, 360), (78729, 360), (78731, 720), (78734, 360), (78735, 360), (78740, 120), (78741, 360), (78742, 360), (78743, 720), (78745, 720), (78747, 720), (78748, 720), (78749, 720), (78750, 720), (78751, 720), (78774, 180), (78775, 180), (78776, 360), (78777, 360), (78778, 720), (78779, 720), (78782, 360)]

theorem segOK : checkSeg 20 perms 78687 78783 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 78687 78783 12000 52370334960 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 52370334960)
    (SegSum.cons (w := 720) h78687 (SegSum.cons (w := 180) h78718 (SegSum.cons (w := 180) h78719 (SegSum.cons (w := 360) h78727 (SegSum.cons (w := 360) h78729 (SegSum.cons (w := 720) h78731 (SegSum.cons (w := 360) h78734 (SegSum.cons (w := 360) h78735 (SegSum.cons (w := 120) h78740 (SegSum.cons (w := 360) h78741 (SegSum.cons (w := 360) h78742 (SegSum.cons (w := 720) h78743 (SegSum.cons (w := 720) h78745 (SegSum.cons (w := 720) h78747 (SegSum.cons (w := 720) h78748 (SegSum.cons (w := 720) h78749 (SegSum.cons (w := 720) h78750 (SegSum.cons (w := 720) h78751 (SegSum.cons (w := 180) h78774 (SegSum.cons (w := 180) h78775 (SegSum.cons (w := 360) h78776 (SegSum.cons (w := 360) h78777 (SegSum.cons (w := 720) h78778 (SegSum.cons (w := 720) h78779 (SegSum.cons (w := 360) h78782 (show SegSum (P.leaf 36) [] 0 from rfl)))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S47
