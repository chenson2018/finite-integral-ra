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

namespace RACert.S6N0.C0.S58

open RACert RACert.Problem

theorem cover88822 : P.CoversSplit 26 10 88822 0xcc00cc00cc00c800cc00cc00cc00c80000000000000000000000000000000000cc00c800cc00c800c000c000c000c0000000000000000000000000000000000000000000003300320000000000330030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 587, 874, 922, 972, 979, 1315, 1658]) (by decide +kernel)

theorem c88822_0 : P.sumLeaves 26 90953728 1024 = 12948954 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88822) (lo := 0) (len := 1024) (W := 12948954) check rows elimOK (by decide) (by decide) cover88822 (by decide)
  decide +kernel

theorem h88822 : P.leaf 36 88822 = 12948954 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 12948954)]) (.cons c88822_0 (.nil)) (by decide) (by decide))

theorem cover88823 : P.CoversSplit 26 10 88823 0xcc00cc00cc00c800cc00cc00cc00c80000000000000000000000000000000000cc00c800cc00c800c000c000c000c0000000000000000000000000000000000000000000003300320000000000330030000000000000000000000000000000000000000000330032000000000030003000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 587, 922, 972, 979, 1315, 1658]) (by decide +kernel)

theorem c88823_0 : P.sumLeaves 26 90954752 128 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88823) (lo := 0) (len := 128) (W := 0) check rows elimOK (by decide) (by decide) cover88823 (by decide)
  decide +kernel

theorem contract88823_1 : P.leaf 32 1421170 = 3106 := by
  apply (leaf_contract (k := 32) (b := 17) (H := 1421170) (ss := [(22, 1, 433), (2, 1, 482), (3, 1, 537), (4, 1, 580), (6, 1, 636), (7, 1, 825), (12, 1, 929), (29, 0, 979), (9, 0, 587), (31, 0, 587), (33, 0, 587), (8, 1, 1217), (19, 1, 1273), (30, 1, 1658), (20, 0, 1665)]) (ids := [3, 8, 9, 11, 12, 13, 14, 15, 16, 19, 21, 22, 23, 24, 25, 26, 30]) (cs := [1, 1, 1, 2, 1, 1, 1, 0, 3, 4, 1, 5, 6, 7, 8, 9, 10, 1, 0, 11, 1, 12, 13, 14, 15, 16, 17, 0, 1, 0, 18, 0]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c88823_1 : P.sumLeaves 26 90954880 64 = 3106 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1421170) rows (by decide) (by decide)).symm.trans contract88823_1

theorem contract88823_2 : P.leaf 32 1421171 = 7487 := by
  apply (leaf_contract (k := 32) (b := 18) (H := 1421171) (ss := [(22, 1, 433), (2, 1, 482), (3, 1, 537), (4, 1, 580), (6, 1, 636), (7, 1, 825), (12, 1, 929), (29, 0, 979), (9, 0, 587), (31, 0, 587), (33, 0, 587), (8, 1, 1217), (19, 1, 1273), (20, 0, 1665)]) (ids := [3, 8, 9, 11, 12, 13, 14, 15, 16, 19, 21, 22, 23, 24, 25, 26, 28, 30]) (cs := [1, 1, 1, 2, 1, 1, 1, 0, 3, 4, 1, 5, 6, 7, 8, 9, 10, 1, 0, 11, 1, 12, 13, 14, 15, 16, 17, 0, 18, 0, 19, 0]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c88823_2 : P.sumLeaves 26 90954944 64 = 7487 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1421171) rows (by decide) (by decide)).symm.trans contract88823_2

theorem c88823_3 : P.sumLeaves 26 90955008 768 = 25617204 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88823) (lo := 256) (len := 768) (W := 25617204) check rows elimOK (by decide) (by decide) cover88823 (by decide)
  decide +kernel

theorem h88823 : P.leaf 36 88823 = 25627797 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(128, 0), (64, 3106), (64, 7487), (768, 25617204)]) (.cons c88823_0 (.cons c88823_1 (.cons c88823_2 (.cons c88823_3 (.nil))))) (by decide) (by decide))

theorem cover88825 : P.CoversSplit 26 10 88825 0xf0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f000000000000000000000000030303000000000000000000000005050000050500000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 587, 922, 923, 972, 979, 1322, 1658, 1665]) (by decide +kernel)

theorem c88825_0 : P.sumLeaves 26 90956800 768 = 60686 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88825) (lo := 0) (len := 768) (W := 60686) check rows elimOK (by decide) (by decide) cover88825 (by decide)
  decide +kernel

theorem contract88825_1 : P.leaf 32 1421212 = 85872 := by
  exact leaf_contract_factors (k := 32) (b := 20) (H := 1421212) (ss := [(7, 1, 487), (21, 1, 586), (9, 1, 473), (15, 1, 473), (11, 1, 817), (12, 1, 817), (19, 1, 865), (10, 1, 867), (20, 1, 915), (30, 1, 1658), (29, 0, 1665), (33, 0, 1665)]) (ids := [0, 1, 2, 3, 4, 6, 11, 12, 14, 15, 16, 20, 22, 24, 25, 26, 29, 30, 21, 23]) (cs := [2, 3, 4, 5, 6, 1, 7, 1, 1, 1, 1, 8, 9, 1, 10, 11, 12, 1, 1, 1, 13, 20, 14, 21, 15, 16, 17, 0, 1, 18, 19, 0]) (bs := [18, 2]) (W := 85872) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c88825_1 : P.sumLeaves 26 90957568 64 = 85872 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1421212) rows (by decide) (by decide)).symm.trans contract88825_1

theorem c88825_2 : P.sumLeaves 26 90957632 192 = 6853094 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88825) (lo := 832) (len := 192) (W := 6853094) check rows elimOK (by decide) (by decide) cover88825 (by decide)
  decide +kernel

theorem h88825 : P.leaf 36 88825 = 6999652 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(768, 60686), (64, 85872), (192, 6853094)]) (.cons c88825_0 (.cons c88825_1 (.cons c88825_2 (.nil)))) (by decide) (by decide))

theorem cover88826 : P.CoversSplit 26 10 88826 0xf0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f000000000000000000000000030303000000000000000000000005050000050500000000000000000000000000000100000000000300030000000000030003000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 587, 874, 972, 979, 1273, 1322, 1658, 1665]) (by decide +kernel)

theorem c88826_0 : P.sumLeaves 26 90957824 1024 = 11696534 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88826) (lo := 0) (len := 1024) (W := 11696534) check rows elimOK (by decide) (by decide) cover88826 (by decide)
  decide +kernel

theorem h88826 : P.leaf 36 88826 = 11696534 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 11696534)]) (.cons c88826_0 (.nil)) (by decide) (by decide))

theorem cover88827 : P.CoversSplit 26 10 88827 0xf0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f000000000000000000000000030303000000000000000000000005050000050500000000000000000000000000000100000000000300030000000000030003000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 587, 922, 972, 979, 1273, 1322, 1658, 1665]) (by decide +kernel)

theorem c88827_0 : P.sumLeaves 26 90958848 1024 = 38368915 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88827) (lo := 0) (len := 1024) (W := 38368915) check rows elimOK (by decide) (by decide) cover88827 (by decide)
  decide +kernel

theorem h88827 : P.leaf 36 88827 = 38368915 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 38368915)]) (.cons c88827_0 (.nil)) (by decide) (by decide))

theorem cover88828 : P.CoversSplit 26 10 88828 0xfffffffffffcfaf8fffffffafffcfaf800000000000000000000000030303000fffffafafffcfaf8f0f0f0f0f0f0f0f00000000000000000000000003030300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 874, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c88828_0 : P.sumLeaves 26 90959872 512 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88828) (lo := 0) (len := 512) (W := 0) check rows elimOK (by decide) (by decide) cover88828 (by decide)
  decide +kernel

theorem contract88828_1 : P.leaf 32 1421256 = 14080 := by
  exact leaf_contract_factors (k := 32) (b := 17) (H := 1421256) (ss := [(2, 1, 474), (7, 1, 487), (21, 1, 524), (9, 1, 473), (15, 1, 473), (4, 1, 580), (11, 1, 817), (12, 1, 817), (19, 1, 865), (14, 1, 866), (10, 1, 867), (20, 1, 915), (30, 1, 922), (29, 0, 1665), (33, 0, 1665)]) (ids := [1, 4, 6, 11, 14, 15, 16, 20, 22, 24, 25, 26, 29, 30, 3, 21, 23]) (cs := [1, 2, 1, 16, 3, 1, 4, 1, 1, 1, 1, 5, 1, 1, 6, 7, 8, 1, 1, 1, 9, 17, 10, 18, 11, 12, 13, 0, 1, 14, 15, 0]) (bs := [14, 3]) (W := 14080) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c88828_1 : P.sumLeaves 26 90960384 64 = 14080 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1421256) rows (by decide) (by decide)).symm.trans contract88828_1

theorem c88828_2 : P.sumLeaves 26 90960448 192 = 1751438 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88828) (lo := 576) (len := 192) (W := 1751438) check rows elimOK (by decide) (by decide) cover88828 (by decide)
  decide +kernel

theorem contract88828_3 : P.leaf 32 1421260 = 44328 := by
  exact leaf_contract_factors (k := 32) (b := 18) (H := 1421260) (ss := [(2, 1, 474), (7, 1, 487), (21, 1, 524), (9, 1, 473), (15, 1, 473), (11, 1, 817), (12, 1, 817), (19, 1, 865), (14, 1, 866), (10, 1, 867), (20, 1, 915), (30, 1, 1658), (29, 0, 1665), (33, 0, 1665)]) (ids := [1, 2, 3, 4, 6, 11, 14, 15, 16, 20, 22, 24, 25, 26, 29, 30, 21, 23]) (cs := [1, 2, 3, 4, 5, 1, 6, 1, 1, 1, 1, 7, 1, 1, 8, 9, 10, 1, 1, 1, 11, 18, 12, 19, 13, 14, 15, 0, 1, 16, 17, 0]) (bs := [16, 2]) (W := 44328) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c88828_3 : P.sumLeaves 26 90960640 64 = 44328 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1421260) rows (by decide) (by decide)).symm.trans contract88828_3

theorem c88828_4 : P.sumLeaves 26 90960704 176 = 5074588 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88828) (lo := 832) (len := 176) (W := 5074588) check rows elimOK (by decide) (by decide) cover88828 (by decide)
  decide +kernel

theorem c88828_5 : P.sumLeaves 26 90960880 16 = 2091720 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88828) (lo := 1008) (len := 16) (W := 2091720) check rows elimOK (by decide) (by decide) cover88828 (by decide)
  decide +kernel

theorem h88828 : P.leaf 36 88828 = 8976154 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(512, 0), (64, 14080), (192, 1751438), (64, 44328), (176, 5074588), (16, 2091720)]) (.cons c88828_0 (.cons c88828_1 (.cons c88828_2 (.cons c88828_3 (.cons c88828_4 (.cons c88828_5 (.nil))))))) (by decide) (by decide))

theorem cover88829 : P.CoversSplit 26 10 88829 0xfffffffffffcfaf8fffffffafffcfaf800000000000000000000000030303000fffffafafffcfaf8f0f0f0f0f0f0f0f00000000000000000000000003030300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c88829_0 : P.sumLeaves 26 90960896 797 = 4945368 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88829) (lo := 0) (len := 797) (W := 4945368) check rows elimOK (by decide) (by decide) cover88829 (by decide)
  decide +kernel

theorem c88829_1 : P.sumLeaves 26 90961693 210 = 14399984 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88829) (lo := 797) (len := 210) (W := 14399984) check rows elimOK (by decide) (by decide) cover88829 (by decide)
  decide +kernel

theorem c88829_2 : P.sumLeaves 26 90961903 17 = 3618596 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88829) (lo := 1007) (len := 17) (W := 3618596) check rows elimOK (by decide) (by decide) cover88829 (by decide)
  decide +kernel

theorem h88829 : P.leaf 36 88829 = 22963948 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(797, 4945368), (210, 14399984), (17, 3618596)]) (.cons c88829_0 (.cons c88829_1 (.cons c88829_2 (.nil)))) (by decide) (by decide))

theorem cover88830 : P.CoversSplit 26 10 88830 0xfffffffffffcfaf8fffffffafffcfaf800000000000000000000000030303000fffffafafffcfaf8f0f0f0f0f0f0f0f00000000000000000000000003030300000000000330032000000000033003200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 874, 922, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c88830_0 : P.sumLeaves 26 90961920 759 = 11183182 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88830) (lo := 0) (len := 759) (W := 11183182) check rows elimOK (by decide) (by decide) cover88830 (by decide)
  decide +kernel

theorem c88830_1 : P.sumLeaves 26 90962679 234 = 28583706 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88830) (lo := 759) (len := 234) (W := 28583706) check rows elimOK (by decide) (by decide) cover88830 (by decide)
  decide +kernel

theorem c88830_2 : P.sumLeaves 26 90962913 31 = 20437911 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88830) (lo := 993) (len := 31) (W := 20437911) check rows elimOK (by decide) (by decide) cover88830 (by decide)
  decide +kernel

theorem h88830 : P.leaf 36 88830 = 60204799 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(759, 11183182), (234, 28583706), (31, 20437911)]) (.cons c88830_0 (.cons c88830_1 (.cons c88830_2 (.nil)))) (by decide) (by decide))

theorem cover88831 : P.CoversSplit 26 10 88831 0xfffffffffffcfaf8fffffffafffcfaf800000000000000000000000030303000fffffafafffcfaf8f0f0f0f0f0f0f0f00000000000000000000000003030300000000000330032000000000033003200000000000000000000000000000000000000000033003200000000003000300000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 922, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c88831_0 : P.sumLeaves 26 90962944 128 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88831) (lo := 0) (len := 128) (W := 0) check rows elimOK (by decide) (by decide) cover88831 (by decide)
  decide +kernel

theorem contract88831_1 : P.leaf 32 1421298 = 9266 := by
  exact leaf_contract_factors (k := 32) (b := 16) (H := 1421298) (ss := [(22, 1, 433), (2, 1, 482), (3, 1, 531), (4, 1, 580), (6, 1, 636), (7, 1, 825), (12, 1, 929), (8, 1, 1217), (30, 1, 1658), (5, 1, 629), (20, 0, 1665), (9, 0, 1609), (29, 0, 1665), (33, 0, 1665), (31, 1, 587), (19, 1, 1273)]) (ids := [8, 9, 11, 12, 13, 14, 15, 16, 19, 21, 23, 24, 25, 26, 30, 22]) (cs := [1, 1, 1, 1, 1, 1, 1, 0, 2, 3, 1, 4, 5, 6, 7, 8, 9, 1, 0, 10, 1, 11, 17, 12, 13, 14, 15, 0, 1, 1, 16, 0]) (bs := [15, 1]) (W := 9266) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c88831_1 : P.sumLeaves 26 90963072 64 = 9266 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1421298) rows (by decide) (by decide)).symm.trans contract88831_1

theorem contract88831_2 : P.leaf 32 1421299 = 20140 := by
  apply (leaf_contract (k := 32) (b := 18) (H := 1421299) (ss := [(22, 1, 433), (2, 1, 482), (3, 1, 531), (4, 1, 580), (6, 1, 636), (7, 1, 825), (12, 1, 929), (8, 1, 1217), (20, 0, 1665), (9, 0, 1609), (29, 0, 1665), (33, 0, 1665), (31, 1, 587), (19, 1, 1273)]) (ids := [3, 8, 9, 11, 12, 13, 14, 15, 16, 19, 21, 22, 23, 24, 25, 26, 28, 30]) (cs := [1, 1, 1, 2, 1, 1, 1, 0, 3, 4, 1, 5, 6, 7, 8, 9, 10, 1, 0, 11, 1, 12, 13, 14, 15, 16, 17, 0, 18, 1, 19, 0]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c88831_2 : P.sumLeaves 26 90963136 64 = 20140 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1421299) rows (by decide) (by decide)).symm.trans contract88831_2

theorem c88831_3 : P.sumLeaves 26 90963200 503 = 26707856 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88831) (lo := 256) (len := 503) (W := 26707856) check rows elimOK (by decide) (by decide) cover88831 (by decide)
  decide +kernel

theorem c88831_4 : P.sumLeaves 26 90963703 234 = 69173829 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88831) (lo := 759) (len := 234) (W := 69173829) check rows elimOK (by decide) (by decide) cover88831 (by decide)
  decide +kernel

theorem c88831_5 : P.sumLeaves 26 90963937 31 = 32796942 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88831) (lo := 993) (len := 31) (W := 32796942) check rows elimOK (by decide) (by decide) cover88831 (by decide)
  decide +kernel

theorem h88831 : P.leaf 36 88831 = 128708033 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(128, 0), (64, 9266), (64, 20140), (503, 26707856), (234, 69173829), (31, 32796942)]) (.cons c88831_0 (.cons c88831_1 (.cons c88831_2 (.cons c88831_3 (.cons c88831_4 (.cons c88831_5 (.nil))))))) (by decide) (by decide))

theorem cover88979 : P.CoversSplit 26 10 88979 0x8000000000000000800000000000000080000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 530, 538, 608, 615, 972, 979, 1315]) (by decide +kernel)

noncomputable def f88979 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (91114496 + i)

theorem c88979_0 : rowSum f88979 0 1024 = 1205480 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 88979) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover88979 (by decide)
  decide +kernel

theorem sum88979 : rowSum f88979 0 1024 = 1205480 :=
  c88979_0

theorem h88979 : P.leaf 36 88979 = 1205480 :=
  leaf_weighted (k := 26) (d := 10) (H := 88979) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 88979) (by decide) (by decide +kernel)) sum88979

theorem cover88981 : P.CoversSplit 26 10 88981 0xcc00000000000000cc00000000000000cc00000000000003c80000000000000000000c0000000000000000000000000000000c0000000003000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [489, 530, 538, 922, 923, 972, 979, 1315, 1322, 1658]) (ps := [(18, [1266], [1315])]) (by decide +kernel)

theorem c88981_0 : P.sumLeaves 26 91116544 1024 = 687608 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88981) (lo := 0) (len := 1024) (W := 687608) check rows elimOK (by decide) (by decide) cover88981 (by decide)
  decide +kernel

theorem h88981 : P.leaf 36 88981 = 687608 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 687608)]) (.cons c88981_0 (.nil)) (by decide) (by decide))

theorem cover88983 : P.CoversSplit 26 10 88983 0xcc00000000000000cc00000000000000cc00000000000003c80000000000000000000c0000000000000000000000000000000c0000000003000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [489, 530, 538, 922, 972, 979, 1315, 1322, 1658]) (ps := [(18, [1266], [1315])]) (by decide +kernel)

theorem c88983_0 : P.sumLeaves 26 91118592 1024 = 12231677 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88983) (lo := 0) (len := 1024) (W := 12231677) check rows elimOK (by decide) (by decide) cover88983 (by decide)
  decide +kernel

theorem h88983 : P.leaf 36 88983 = 12231677 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 12231677)]) (.cons c88983_0 (.nil)) (by decide) (by decide))

theorem cover88985 : P.CoversSplit 26 10 88985 0xa0a0000000000000a0a0000000000000a0a0000000000000a0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 538, 615, 922, 923, 972, 1315]) (by decide +kernel)

theorem c88985_0 : P.sumLeaves 26 91120640 1024 = 990432 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88985) (lo := 0) (len := 1024) (W := 990432) check rows elimOK (by decide) (by decide) cover88985 (by decide)
  decide +kernel

theorem h88985 : P.leaf 36 88985 = 990432 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 990432)]) (.cons c88985_0 (.nil)) (by decide) (by decide))

theorem cover88986 : P.CoversSplit 26 10 88986 0xa0a0000000000000a0a0000000000000a0a0000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 538, 615, 874, 922, 972, 1315, 1322]) (by decide +kernel)

theorem c88986_0 : P.sumLeaves 26 91121664 768 = 26496 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88986) (lo := 0) (len := 768) (W := 26496) check rows elimOK (by decide) (by decide) cover88986 (by decide)
  decide +kernel

theorem contract88986_1 : P.leaf 32 1423788 = 88448 := by
  exact leaf_contract_factors (k := 32) (b := 19) (H := 1423788) (ss := [(8, 1, 479), (28, 1, 481), (30, 1, 481), (3, 1, 531), (33, 1, 537), (14, 1, 866), (18, 1, 517), (10, 1, 867), (11, 1, 817), (7, 1, 460), (12, 1, 460), (16, 1, 1210), (32, 1, 1315)]) (ids := [0, 2, 3, 4, 7, 11, 13, 15, 17, 18, 19, 20, 23, 25, 27, 29, 21, 22, 24]) (cs := [2, 1, 3, 4, 5, 1, 1, 6, 1, 1, 1, 7, 1, 8, 1, 9, 1, 10, 11, 12, 13, 18, 19, 14, 20, 15, 1, 16, 1, 17, 1, 1]) (bs := [16, 3]) (W := 88448) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c88986_1 : P.sumLeaves 26 91122432 64 = 88448 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1423788) rows (by decide) (by decide)).symm.trans contract88986_1

theorem contract88986_2 : P.leaf 32 1423789 = 120832 := by
  exact leaf_contract_factors (k := 32) (b := 19) (H := 1423789) (ss := [(8, 1, 479), (28, 1, 481), (30, 1, 481), (3, 1, 531), (33, 1, 537), (10, 1, 867), (11, 1, 817), (7, 1, 460), (12, 1, 460), (16, 1, 1210), (14, 1, 465), (18, 1, 517), (32, 1, 1315)]) (ids := [0, 2, 3, 4, 7, 11, 13, 15, 17, 18, 19, 20, 23, 25, 27, 29, 21, 22, 24]) (cs := [2, 1, 3, 4, 5, 1, 1, 6, 1, 1, 1, 7, 1, 8, 1, 9, 1, 10, 11, 12, 13, 18, 19, 14, 20, 15, 1, 16, 1, 17, 1, 1]) (bs := [16, 3]) (W := 120832) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c88986_2 : P.sumLeaves 26 91122496 64 = 120832 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1423789) rows (by decide) (by decide)).symm.trans contract88986_2

theorem contract88986_3 : P.leaf 32 1423790 = 220264 := by
  exact leaf_contract_factors (k := 32) (b := 20) (H := 1423790) (ss := [(8, 1, 479), (28, 1, 481), (30, 1, 481), (3, 1, 531), (33, 1, 537), (14, 1, 866), (18, 1, 517), (12, 1, 929), (7, 1, 460), (11, 1, 817), (16, 1, 1210), (32, 1, 1315)]) (ids := [0, 2, 3, 4, 7, 8, 11, 13, 15, 17, 18, 19, 20, 21, 23, 25, 27, 29, 22, 24]) (cs := [2, 1, 3, 4, 5, 1, 1, 6, 7, 1, 1, 8, 1, 9, 1, 10, 1, 11, 12, 13, 14, 15, 20, 16, 21, 17, 1, 18, 1, 19, 1, 1]) (bs := [18, 2]) (W := 220264) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c88986_3 : P.sumLeaves 26 91122560 64 = 220264 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1423790) rows (by decide) (by decide)).symm.trans contract88986_3

theorem contract88986_4 : P.leaf 32 1423791 = 287256 := by
  exact leaf_contract_factors (k := 32) (b := 20) (H := 1423791) (ss := [(8, 1, 479), (28, 1, 481), (30, 1, 481), (3, 1, 531), (33, 1, 537), (12, 1, 929), (7, 1, 460), (11, 1, 817), (16, 1, 1210), (14, 1, 465), (18, 1, 517), (32, 1, 1315)]) (ids := [0, 2, 3, 4, 7, 8, 11, 13, 15, 17, 18, 19, 20, 21, 23, 25, 27, 29, 22, 24]) (cs := [2, 1, 3, 4, 5, 1, 1, 6, 7, 1, 1, 8, 1, 9, 1, 10, 1, 11, 12, 13, 14, 15, 20, 16, 21, 17, 1, 18, 1, 19, 1, 1]) (bs := [18, 2]) (W := 287256) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c88986_4 : P.sumLeaves 26 91122624 64 = 287256 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1423791) rows (by decide) (by decide)).symm.trans contract88986_4

theorem h88986 : P.leaf 36 88986 = 743296 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(768, 26496), (64, 88448), (64, 120832), (64, 220264), (64, 287256)]) (.cons c88986_0 (.cons c88986_1 (.cons c88986_2 (.cons c88986_3 (.cons c88986_4 (.nil)))))) (by decide) (by decide))

theorem cover88987 : P.CoversSplit 26 10 88987 0xa0a0000000000000a0a0000000000000a0a0000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 538, 615, 972, 1315, 1322]) (by decide +kernel)

theorem c88987_0 : P.sumLeaves 26 91122688 1024 = 8369676 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88987) (lo := 0) (len := 1024) (W := 8369676) check rows elimOK (by decide) (by decide) cover88987 (by decide)
  decide +kernel

theorem h88987 : P.leaf 36 88987 = 8369676 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8369676)]) (.cons c88987_0 (.nil)) (by decide) (by decide))

theorem cover88988 : P.CoversSplit 26 10 88988 0xffff000000000000ffff000000000000ffff00000000000cfafa00000000000800000f0f00000000000000000000000000000f0f0000000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [530, 538, 874, 922, 923, 979, 1315, 1322, 1658]) (ps := [(18, [1266], [1315])]) (by decide +kernel)

theorem c88988_0 : P.sumLeaves 26 91123712 576 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88988) (lo := 0) (len := 576) (W := 0) check rows elimOK (by decide) (by decide) cover88988 (by decide)
  decide +kernel

theorem contract88988_1 : P.leaf 32 1423817 = 6112 := by
  exact leaf_contract_factors (k := 32) (b := 16) (H := 1423817) (ss := [(15, 1, 472), (3, 1, 531), (10, 1, 867), (11, 1, 817), (12, 1, 817), (19, 1, 865), (20, 1, 915), (18, 1, 1266), (8, 1, 465), (14, 1, 465), (2, 1, 409), (16, 1, 1210), (30, 0, 1315), (32, 0, 1315), (7, 1, 467), (26, 1, 873)]) (ids := [2, 3, 4, 7, 15, 19, 20, 25, 26, 27, 29, 31, 11, 21, 22, 23]) (cs := [1, 1, 2, 3, 4, 1, 1, 5, 1, 1, 1, 14, 1, 1, 1, 6, 1, 1, 1, 7, 8, 15, 16, 17, 1, 9, 10, 11, 0, 12, 0, 13]) (bs := [12, 4]) (W := 6112) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c88988_1 : P.sumLeaves 26 91124288 64 = 6112 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1423817) rows (by decide) (by decide)).symm.trans contract88988_1

theorem c88988_2 : P.sumLeaves 26 91124352 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88988) (lo := 640) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover88988 (by decide)
  decide +kernel

theorem contract88988_3 : P.leaf 32 1423819 = 15040 := by
  exact leaf_contract_factors (k := 32) (b := 16) (H := 1423819) (ss := [(15, 1, 472), (3, 1, 531), (18, 1, 1266), (8, 1, 465), (14, 1, 465), (2, 1, 409), (16, 1, 1210), (30, 0, 1315), (32, 0, 1315), (7, 1, 467), (11, 1, 817), (12, 1, 817), (26, 1, 873), (20, 1, 915), (19, 1, 865), (33, 1, 1322)]) (ids := [4, 20, 27, 7, 8, 11, 15, 19, 21, 26, 2, 3, 22, 23, 25, 29]) (cs := [1, 1, 12, 13, 2, 1, 1, 5, 6, 1, 1, 7, 1, 1, 1, 8, 1, 1, 1, 9, 3, 10, 14, 15, 1, 16, 11, 4, 0, 17, 0, 1]) (bs := [3, 7, 6]) (W := 15040) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c88988_3 : P.sumLeaves 26 91124416 64 = 15040 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1423819) rows (by decide) (by decide)).symm.trans contract88988_3

theorem contract88988_4 : P.leaf 32 1423820 = 71776 := by
  exact leaf_contract_factors (k := 32) (b := 20) (H := 1423820) (ss := [(15, 1, 472), (2, 1, 474), (3, 1, 531), (14, 1, 866), (8, 1, 517), (18, 1, 517), (10, 1, 867), (11, 1, 817), (12, 1, 817), (19, 1, 865), (20, 1, 915), (16, 1, 1210)]) (ids := [2, 3, 4, 5, 7, 11, 15, 19, 20, 21, 24, 25, 26, 27, 28, 29, 30, 31, 22, 23]) (cs := [1, 1, 2, 3, 4, 5, 1, 6, 1, 1, 1, 7, 1, 1, 1, 8, 1, 1, 1, 9, 10, 11, 20, 21, 12, 13, 14, 15, 16, 17, 18, 19]) (bs := [18, 2]) (W := 71776) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c88988_4 : P.sumLeaves 26 91124480 64 = 71776 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1423820) rows (by decide) (by decide)).symm.trans contract88988_4

theorem contract88988_5 : P.leaf 32 1423821 = 91616 := by
  exact leaf_contract_factors (k := 32) (b := 20) (H := 1423821) (ss := [(15, 1, 472), (3, 1, 531), (10, 1, 867), (11, 1, 817), (12, 1, 817), (19, 1, 865), (20, 1, 915), (18, 1, 1266), (8, 1, 465), (14, 1, 465), (2, 1, 409), (16, 1, 1210)]) (ids := [2, 3, 4, 5, 7, 15, 19, 20, 21, 25, 26, 27, 28, 29, 30, 31, 11, 22, 23, 24]) (cs := [1, 1, 2, 3, 4, 5, 1, 6, 1, 1, 1, 18, 1, 1, 1, 7, 1, 1, 1, 8, 9, 10, 19, 20, 21, 11, 12, 13, 14, 15, 16, 17]) (bs := [16, 4]) (W := 91616) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c88988_5 : P.sumLeaves 26 91124544 64 = 91616 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1423821) rows (by decide) (by decide)).symm.trans contract88988_5

theorem c88988_6 : P.sumLeaves 26 91124608 128 = 739584 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88988) (lo := 896) (len := 128) (W := 739584) check rows elimOK (by decide) (by decide) cover88988 (by decide)
  decide +kernel

theorem h88988 : P.leaf 36 88988 = 924128 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(576, 0), (64, 6112), (64, 0), (64, 15040), (64, 71776), (64, 91616), (128, 739584)]) (.cons c88988_0 (.cons c88988_1 (.cons c88988_2 (.cons c88988_3 (.cons c88988_4 (.cons c88988_5 (.cons c88988_6 (.nil)))))))) (by decide) (by decide))

theorem cover88989 : P.CoversSplit 26 10 88989 0xffff000000000000ffff000000000000ffff00000000000cfafa00000000000800000f0f00000000000000000000000000000f0f0000000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [530, 538, 922, 923, 979, 1315, 1322, 1658]) (ps := [(18, [1266], [1315])]) (by decide +kernel)

theorem c88989_0 : P.sumLeaves 26 91124736 1024 = 5515996 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88989) (lo := 0) (len := 1024) (W := 5515996) check rows elimOK (by decide) (by decide) cover88989 (by decide)
  decide +kernel

theorem h88989 : P.leaf 36 88989 = 5515996 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5515996)]) (.cons c88989_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(88822, 720), (88823, 720), (88825, 360), (88826, 720), (88827, 720), (88828, 720), (88829, 720), (88830, 720), (88831, 720), (88979, 360), (88981, 720), (88983, 720), (88985, 720), (88986, 720), (88987, 720), (88988, 720), (88989, 720)]

theorem segOK : checkSeg 20 perms 88822 88990 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 88822 88990 11520 247003569360 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 247003569360)
    (SegSum.cons (w := 720) h88822 (SegSum.cons (w := 720) h88823 (SegSum.cons (w := 360) h88825 (SegSum.cons (w := 720) h88826 (SegSum.cons (w := 720) h88827 (SegSum.cons (w := 720) h88828 (SegSum.cons (w := 720) h88829 (SegSum.cons (w := 720) h88830 (SegSum.cons (w := 720) h88831 (SegSum.cons (w := 360) h88979 (SegSum.cons (w := 720) h88981 (SegSum.cons (w := 720) h88983 (SegSum.cons (w := 720) h88985 (SegSum.cons (w := 720) h88986 (SegSum.cons (w := 720) h88987 (SegSum.cons (w := 720) h88988 (SegSum.cons (w := 720) h88989 (show SegSum (P.leaf 36) [] 0 from rfl)))))))))))))))))) (by decide)

end RACert.S6N0.C0.S58
