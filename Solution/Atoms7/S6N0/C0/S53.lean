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

namespace RACert.S6N0.C0.S53

open RACert RACert.Problem

theorem cover79726 : P.CoversSplit 26 10 79726 0xfffffffafffffafa0000000000000000fffcfff8fffcc8c85554555055004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 873, 874, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c79726_0 : P.sumLeaves 26 81639424 997 = 17143584 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79726) (lo := 0) (len := 997) (W := 17143584) check rows elimOK (by decide) (by decide) cover79726 (by decide)
  decide +kernel

theorem c79726_1 : P.sumLeaves 26 81640421 27 = 14852286 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79726) (lo := 997) (len := 27) (W := 14852286) check rows elimOK (by decide) (by decide) cover79726 (by decide)
  decide +kernel

theorem h79726 : P.leaf 36 79726 = 31995870 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(997, 17143584), (27, 14852286)]) (.cons c79726_0 (.cons c79726_1 (.nil))) (by decide) (by decide))

theorem cover79727 : P.CoversSplit 26 10 79727 0xfffffffafffffafa0000000000000000fffcfff8fffcc8c855545550550040000000000000000000000000000000000000000000000000000000000000000000fffffffafffffafa0000000000000000ffccffc8cc00c80055445540440040000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 930, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c79727_0 : P.sumLeaves 26 81640448 506 = 27905826 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79727) (lo := 0) (len := 506) (W := 27905826) check rows elimOK (by decide) (by decide) cover79727 (by decide)
  decide +kernel

theorem c79727_1 : P.sumLeaves 26 81640954 483 = 33873408 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79727) (lo := 506) (len := 483) (W := 33873408) check rows elimOK (by decide) (by decide) cover79727 (by decide)
  decide +kernel

theorem c79727_2 : P.sumLeaves 26 81641437 35 = 28846080 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79727) (lo := 989) (len := 35) (W := 28846080) check rows elimOK (by decide) (by decide) cover79727 (by decide)
  decide +kernel

theorem h79727 : P.leaf 36 79727 = 90625314 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(506, 27905826), (483, 33873408), (35, 28846080)]) (.cons c79727_0 (.cons c79727_1 (.cons c79727_2 (.nil)))) (by decide) (by decide))

theorem cover79742 : P.CoversSplit 26 10 79742 0xfffffffafffffafa0000000000000000fffcfff8fffcc8c85554555055004000555550505555505055555050555550505554505055544040555450505500400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 873, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c79742_0 : P.sumLeaves 26 81655808 820 = 22067793 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79742) (lo := 0) (len := 820) (W := 22067793) check rows elimOK (by decide) (by decide) cover79742 (by decide)
  decide +kernel

theorem c79742_1 : P.sumLeaves 26 81656628 189 = 71413908 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79742) (lo := 820) (len := 189) (W := 71413908) check rows elimOK (by decide) (by decide) cover79742 (by decide)
  decide +kernel

theorem c79742_2 : P.sumLeaves 26 81656817 15 = 29090336 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79742) (lo := 1009) (len := 15) (W := 29090336) check rows elimOK (by decide) (by decide) cover79742 (by decide)
  decide +kernel

theorem h79742 : P.leaf 36 79742 = 122572037 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(820, 22067793), (189, 71413908), (15, 29090336)]) (.cons c79742_0 (.cons c79742_1 (.cons c79742_2 (.nil)))) (by decide) (by decide))

theorem cover79743 : P.CoversSplit 26 10 79743 0xfffffffafffffafa0000000000000000fffcfff8fffcc8c855545550550040005555505055555050555550505555505055545050555440405554505055004000fffffffafffffafa0000000000000000ffccffc8cc00c80055445540440040005555505055555050555550505555505055445040440040005544504044004000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c79743_0 : P.sumLeaves 26 81656832 360 = 15968591 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79743) (lo := 0) (len := 360) (W := 15968591) check rows elimOK (by decide) (by decide) cover79743 (by decide)
  decide +kernel

theorem c79743_1 : P.sumLeaves 26 81657192 234 = 87151239 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79743) (lo := 360) (len := 234) (W := 87151239) check rows elimOK (by decide) (by decide) cover79743 (by decide)
  decide +kernel

theorem c79743_2 : P.sumLeaves 26 81657426 262 = 52159809 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79743) (lo := 594) (len := 262) (W := 52159809) check rows elimOK (by decide) (by decide) cover79743 (by decide)
  decide +kernel

theorem c79743_3 : P.sumLeaves 26 81657688 168 = 174469865 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79743) (lo := 856) (len := 168) (W := 174469865) check rows elimOK (by decide) (by decide) cover79743 (by decide)
  decide +kernel

theorem h79743 : P.leaf 36 79743 = 329749504 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(360, 15968591), (234, 87151239), (262, 52159809), (168, 174469865)]) (.cons c79743_0 (.cons c79743_1 (.cons c79743_2 (.cons c79743_3 (.nil))))) (by decide) (by decide))

theorem cover79753 : P.CoversSplit 26 10 79753 0xf0f0000000000000f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 538, 566, 923, 972, 979, 1273, 1315, 1322]) (by decide +kernel)

theorem c79753_0 : P.sumLeaves 26 81667072 1024 = 262144 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79753) (lo := 0) (len := 1024) (W := 262144) check rows elimOK (by decide) (by decide) cover79753 (by decide)
  decide +kernel

theorem h79753 : P.leaf 36 79753 = 262144 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 262144)]) (.cons c79753_0 (.nil)) (by decide) (by decide))

theorem cover79755 : P.CoversSplit 26 10 79755 0xf0f0000000000000f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 538, 615, 972, 979, 1266, 1273, 1315, 1322]) (by decide +kernel)

theorem c79755_0 : P.sumLeaves 26 81669120 1024 = 1404928 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79755) (lo := 0) (len := 1024) (W := 1404928) check rows elimOK (by decide) (by decide) cover79755 (by decide)
  decide +kernel

theorem h79755 : P.leaf 36 79755 = 1404928 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1404928)]) (.cons c79755_0 (.nil)) (by decide) (by decide))

theorem cover79757 : P.CoversSplit 26 10 79757 0xffff000000000000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00000000000000880000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 566, 923, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c79757_0 : P.sumLeaves 26 81671168 1024 = 1592448 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79757) (lo := 0) (len := 1024) (W := 1592448) check rows elimOK (by decide) (by decide) cover79757 (by decide)
  decide +kernel

theorem h79757 : P.leaf 36 79757 = 1592448 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1592448)]) (.cons c79757_0 (.nil)) (by decide) (by decide))

theorem cover79759 : P.CoversSplit 26 10 79759 0xffff000000000000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000cc000800880000008800080000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 979, 1266, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c79759_0 : P.sumLeaves 26 81673216 1024 = 5241760 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79759) (lo := 0) (len := 1024) (W := 5241760) check rows elimOK (by decide) (by decide) cover79759 (by decide)
  decide +kernel

theorem h79759 : P.leaf 36 79759 = 5241760 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5241760)]) (.cons c79759_0 (.nil)) (by decide) (by decide))

theorem cover79765 : P.CoversSplit 26 10 79765 0xcc00000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 923, 930, 972, 979, 1315, 1658, 1665]) (by decide +kernel)

theorem c79765_0 : P.sumLeaves 26 81679360 1024 = 778832 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79765) (lo := 0) (len := 1024) (W := 778832) check rows elimOK (by decide) (by decide) cover79765 (by decide)
  decide +kernel

theorem h79765 : P.leaf 36 79765 = 778832 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 778832)]) (.cons c79765_0 (.nil)) (by decide) (by decide))

theorem cover79767 : P.CoversSplit 26 10 79767 0xcc00000000000000cc00000000000000000000000000000000000000000000000c0000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 930, 972, 979, 1315, 1658, 1665]) (by decide +kernel)

theorem c79767_0 : P.sumLeaves 26 81681408 1024 = 3419288 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79767) (lo := 0) (len := 1024) (W := 3419288) check rows elimOK (by decide) (by decide) cover79767 (by decide)
  decide +kernel

theorem h79767 : P.leaf 36 79767 = 3419288 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3419288)]) (.cons c79767_0 (.nil)) (by decide) (by decide))

theorem cover79772 : P.CoversSplit 26 10 79772 0xffff000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [467, 538, 923, 930, 979, 1273, 1322]) (by decide +kernel)

theorem c79772_0 : P.sumLeaves 26 81686528 1024 = 2222272 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79772) (lo := 0) (len := 1024) (W := 2222272) check rows elimOK (by decide) (by decide) cover79772 (by decide)
  decide +kernel

theorem h79772 : P.leaf 36 79772 = 2222272 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2222272)]) (.cons c79772_0 (.nil)) (by decide) (by decide))

theorem cover79773 : P.CoversSplit 26 10 79773 0xffff000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 923, 930, 972, 979, 1273, 1315, 1322]) (by decide +kernel)

theorem c79773_0 : P.sumLeaves 26 81687552 1024 = 8117756 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79773) (lo := 0) (len := 1024) (W := 8117756) check rows elimOK (by decide) (by decide) cover79773 (by decide)
  decide +kernel

theorem h79773 : P.leaf 36 79773 = 8117756 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8117756)]) (.cons c79773_0 (.nil)) (by decide) (by decide))

theorem cover79774 : P.CoversSplit 26 10 79774 0xffff000000000000ffff000000000000000000000000000000000000000000000f0f0a0a000000000a0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 873, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c79774_0 : P.sumLeaves 26 81688576 1024 = 6425864 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79774) (lo := 0) (len := 1024) (W := 6425864) check rows elimOK (by decide) (by decide) cover79774 (by decide)
  decide +kernel

theorem h79774 : P.leaf 36 79774 = 6425864 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6425864)]) (.cons c79774_0 (.nil)) (by decide) (by decide))

theorem cover79775 : P.CoversSplit 26 10 79775 0xffff000000000000ffff000000000000000000000000000000000000000000000f0f0a0a000000000a0a0a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c79775_0 : P.sumLeaves 26 81689600 1024 = 19969964 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79775) (lo := 0) (len := 1024) (W := 19969964) check rows elimOK (by decide) (by decide) cover79775 (by decide)
  decide +kernel

theorem h79775 : P.leaf 36 79775 = 19969964 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 19969964)]) (.cons c79775_0 (.nil)) (by decide) (by decide))

theorem cover79781 : P.CoversSplit 26 10 79781 0xcc00cc0000000000cc00cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 559, 873, 923, 930, 979]) (by decide +kernel)

theorem c79781_0 : P.sumLeaves 26 81695744 1024 = 998592 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79781) (lo := 0) (len := 1024) (W := 998592) check rows elimOK (by decide) (by decide) cover79781 (by decide)
  decide +kernel

theorem h79781 : P.leaf 36 79781 = 998592 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 998592)]) (.cons c79781_0 (.nil)) (by decide) (by decide))

theorem cover79782 : P.CoversSplit 26 10 79782 0xcc00cc0000000000cc00cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 873, 930, 972, 979, 1266, 1273, 1658, 1665]) (by decide +kernel)

theorem c79782_0 : P.sumLeaves 26 81696768 1024 = 452608 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79782) (lo := 0) (len := 1024) (W := 452608) check rows elimOK (by decide) (by decide) cover79782 (by decide)
  decide +kernel

theorem h79782 : P.leaf 36 79782 = 452608 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 452608)]) (.cons c79782_0 (.nil)) (by decide) (by decide))

theorem cover79783 : P.CoversSplit 26 10 79783 0xcc00cc0000000000cc00cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 873, 930, 972, 979, 1266, 1658, 1665]) (by decide +kernel)

theorem c79783_0 : P.sumLeaves 26 81697792 1024 = 3238208 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79783) (lo := 0) (len := 1024) (W := 3238208) check rows elimOK (by decide) (by decide) cover79783 (by decide)
  decide +kernel

theorem h79783 : P.leaf 36 79783 = 3238208 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3238208)]) (.cons c79783_0 (.nil)) (by decide) (by decide))

theorem cover79784 : P.CoversSplit 26 10 79784 0xf0f0f0f000000000f0f0f0f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 509, 538, 566, 874, 923, 1273]) (by decide +kernel)

theorem c79784_0 : P.sumLeaves 26 81698816 1024 = 110080 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79784) (lo := 0) (len := 1024) (W := 110080) check rows elimOK (by decide) (by decide) cover79784 (by decide)
  decide +kernel

theorem h79784 : P.leaf 36 79784 = 110080 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 110080)]) (.cons c79784_0 (.nil)) (by decide) (by decide))

theorem cover79785 : P.CoversSplit 26 10 79785 0xf0f0f0f500000000f0f0f0f50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 566, 923, 972, 979, 1273, 1322]) (by decide +kernel)

theorem c79785_0 : P.sumLeaves 26 81699840 1024 = 1756768 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79785) (lo := 0) (len := 1024) (W := 1756768) check rows elimOK (by decide) (by decide) cover79785 (by decide)
  decide +kernel

theorem h79785 : P.leaf 36 79785 = 1756768 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1756768)]) (.cons c79785_0 (.nil)) (by decide) (by decide))

theorem cover79786 : P.CoversSplit 26 10 79786 0xf0f0f0f000000000f0f0f0f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [479, 538, 874, 972, 1266, 1273]) (by decide +kernel)

theorem c79786_0 : P.sumLeaves 26 81700864 1024 = 1082752 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79786) (lo := 0) (len := 1024) (W := 1082752) check rows elimOK (by decide) (by decide) cover79786 (by decide)
  decide +kernel

theorem h79786 : P.leaf 36 79786 = 1082752 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1082752)]) (.cons c79786_0 (.nil)) (by decide) (by decide))

theorem cover79787 : P.CoversSplit 26 10 79787 0xf0f0f0f500000000f0f0f0f50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 972, 979, 1266, 1273, 1315, 1322]) (by decide +kernel)

theorem c79787_0 : P.sumLeaves 26 81701888 1024 = 6799904 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79787) (lo := 0) (len := 1024) (W := 6799904) check rows elimOK (by decide) (by decide) cover79787 (by decide)
  decide +kernel

theorem h79787 : P.leaf 36 79787 = 6799904 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6799904)]) (.cons c79787_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(79726, 720), (79727, 720), (79742, 360), (79743, 360), (79753, 240), (79755, 240), (79757, 720), (79759, 720), (79765, 720), (79767, 720), (79772, 360), (79773, 720), (79774, 360), (79775, 720), (79781, 360), (79782, 720), (79783, 720), (79784, 720), (79785, 720), (79786, 720), (79787, 720)]

theorem segOK : checkSeg 20 perms 79726 79788 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 79726 79788 12360 292839391560 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 292839391560)
    (SegSum.cons (w := 720) h79726 (SegSum.cons (w := 720) h79727 (SegSum.cons (w := 360) h79742 (SegSum.cons (w := 360) h79743 (SegSum.cons (w := 240) h79753 (SegSum.cons (w := 240) h79755 (SegSum.cons (w := 720) h79757 (SegSum.cons (w := 720) h79759 (SegSum.cons (w := 720) h79765 (SegSum.cons (w := 720) h79767 (SegSum.cons (w := 360) h79772 (SegSum.cons (w := 720) h79773 (SegSum.cons (w := 360) h79774 (SegSum.cons (w := 720) h79775 (SegSum.cons (w := 360) h79781 (SegSum.cons (w := 720) h79782 (SegSum.cons (w := 720) h79783 (SegSum.cons (w := 720) h79784 (SegSum.cons (w := 720) h79785 (SegSum.cons (w := 720) h79786 (SegSum.cons (w := 720) h79787 (show SegSum (P.leaf 36) [] 0 from rfl)))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S53
