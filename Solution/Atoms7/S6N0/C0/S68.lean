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

namespace RACert.S6N0.C0.S68

open RACert RACert.Problem

theorem cover89727 : P.CoversSplit 26 10 89727 0xfffffffffffcfaf800000000000000000000000000000000000000000f0c0a080f0f0a0a0f0c0a080f0f0a0a0f0c0a080000000000000000000000000f0c0a0800000000ffccfac8000000000000000000000000ffccfac8000000000f0c0a08000000000f0c0a08000000000f0c0a08000000000f0c0a08000000000f0c0a08 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 587, 979, 1315, 1658, 1665]) (by decide +kernel)

theorem c89727_0 : P.sumLeaves 26 91880448 643 = 12732268 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89727) (lo := 0) (len := 643) (W := 12732268) check rows elimOK (by decide) (by decide) cover89727 (by decide)
  decide +kernel

theorem c89727_1 : P.sumLeaves 26 91881091 369 = 47858944 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89727) (lo := 643) (len := 369) (W := 47858944) check rows elimOK (by decide) (by decide) cover89727 (by decide)
  decide +kernel

theorem c89727_2 : P.sumLeaves 26 91881460 12 = 12642984 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89727) (lo := 1012) (len := 12) (W := 12642984) check rows elimOK (by decide) (by decide) cover89727 (by decide)
  decide +kernel

theorem h89727 : P.leaf 36 89727 = 73234196 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(643, 12732268), (369, 47858944), (12, 12642984)]) (.cons c89727_0 (.cons c89727_1 (.cons c89727_2 (.nil)))) (by decide) (by decide))

theorem cover89812 : P.CoversSplit 26 10 89812 0xcc000000cc000400cc000000cc00040000000000000000000000000000000000040004000400040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 587, 874, 922, 923, 972, 979, 1315, 1658]) (by decide +kernel)

theorem c89812_0 : P.sumLeaves 26 91967488 1024 = 694112 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89812) (lo := 0) (len := 1024) (W := 694112) check rows elimOK (by decide) (by decide) cover89812 (by decide)
  decide +kernel

theorem h89812 : P.leaf 36 89812 = 694112 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 694112)]) (.cons c89812_0 (.nil)) (by decide) (by decide))

theorem cover89813 : P.CoversSplit 26 10 89813 0xcc000000cc000400cc000000cc00040000000000000000000000000000000000040004000400040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 587, 922, 923, 972, 979, 1315, 1658]) (by decide +kernel)

theorem c89813_0 : P.sumLeaves 26 91968512 1024 = 6571223 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89813) (lo := 0) (len := 1024) (W := 6571223) check rows elimOK (by decide) (by decide) cover89813 (by decide)
  decide +kernel

theorem h89813 : P.leaf 36 89813 = 6571223 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6571223)]) (.cons c89813_0 (.nil)) (by decide) (by decide))

theorem cover89814 : P.CoversSplit 26 10 89814 0xcc000000cc000400cc000000cc00040000000000000000000000000000000000040004000400040000000000000000000000000000000000000000000000000000000000003300010000000000330000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 587, 874, 972, 979, 1315, 1658]) (by decide +kernel)

theorem c89814_0 : P.sumLeaves 26 91969536 1024 = 13537989 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89814) (lo := 0) (len := 1024) (W := 13537989) check rows elimOK (by decide) (by decide) cover89814 (by decide)
  decide +kernel

theorem h89814 : P.leaf 36 89814 = 13537989 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 13537989)]) (.cons c89814_0 (.nil)) (by decide) (by decide))

theorem cover89815 : P.CoversSplit 26 10 89815 0xcc000000cc000400cc000000cc00040000000000000000000000000000000000040004000400040000000000000000000000000000000000000000000000000000000000003300010000000000330000000000000000000000000000000000000000000000010001000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 587, 972, 979, 1315, 1658]) (by decide +kernel)

theorem c89815_0 : P.sumLeaves 26 91970560 1024 = 28272573 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89815) (lo := 0) (len := 1024) (W := 28272573) check rows elimOK (by decide) (by decide) cover89815 (by decide)
  decide +kernel

theorem h89815 : P.leaf 36 89815 = 28272573 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 28272573)]) (.cons c89815_0 (.nil)) (by decide) (by decide))

theorem cover89818 : P.CoversSplit 26 10 89818 0xa0a00000a0a00000a0a00000a0a0000000000000000000000000000020200000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000020000000000000002000000000000000200000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 587, 874, 972, 979, 1315, 1665]) (by decide +kernel)

theorem c89818_0 : P.sumLeaves 26 91973632 1024 = 7346364 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89818) (lo := 0) (len := 1024) (W := 7346364) check rows elimOK (by decide) (by decide) cover89818 (by decide)
  decide +kernel

theorem h89818 : P.leaf 36 89818 = 7346364 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 7346364)]) (.cons c89818_0 (.nil)) (by decide) (by decide))

theorem cover89819 : P.CoversSplit 26 10 89819 0xa0a00000a0a00000a0a00000a0a0000000000000000000000000000020200000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000020000000000000002000000000000000200000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 587, 972, 979, 1315, 1665]) (by decide +kernel)

theorem c89819_0 : P.sumLeaves 26 91974656 1024 = 27732640 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89819) (lo := 0) (len := 1024) (W := 27732640) check rows elimOK (by decide) (by decide) cover89819 (by decide)
  decide +kernel

theorem h89819 : P.leaf 36 89819 = 27732640 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 27732640)]) (.cons c89819_0 (.nil)) (by decide) (by decide))

theorem cover89820 : P.CoversSplit 26 10 89820 0xffff0000fffc0504ffff0000fffc050000000000000000000000000030300000050505050504050400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 587, 874, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89820_0 : P.sumLeaves 26 91975680 1024 = 20914803 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89820) (lo := 0) (len := 1024) (W := 20914803) check rows elimOK (by decide) (by decide) cover89820 (by decide)
  decide +kernel

theorem h89820 : P.leaf 36 89820 = 20914803 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 20914803)]) (.cons c89820_0 (.nil)) (by decide) (by decide))

theorem cover89821 : P.CoversSplit 26 10 89821 0xffff0000fffc0504ffff0000fffc050000000000000000000000000030300000050505050504050400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 587, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89821_0 : P.sumLeaves 26 91976704 1024 = 48314406 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89821) (lo := 0) (len := 1024) (W := 48314406) check rows elimOK (by decide) (by decide) cover89821 (by decide)
  decide +kernel

theorem h89821 : P.leaf 36 89821 = 48314406 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 48314406)]) (.cons c89821_0 (.nil)) (by decide) (by decide))

theorem cover89822 : P.CoversSplit 26 10 89822 0xffff0000fffc0504ffff0000fffc050000000000000000000000000030300000050505050504050400000000000000000000000000000000000000000000000000000000330001000000000033000100000000003300010000000000300000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 587, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89822_0 : P.sumLeaves 26 91977728 1020 = 60696676 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89822) (lo := 0) (len := 1020) (W := 60696676) check rows elimOK (by decide) (by decide) cover89822 (by decide)
  decide +kernel

theorem c89822_1 : P.sumLeaves 26 91978748 4 = 8192360 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89822) (lo := 1020) (len := 4) (W := 8192360) check rows elimOK (by decide) (by decide) cover89822 (by decide)
  decide +kernel

theorem h89822 : P.leaf 36 89822 = 68889036 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1020, 60696676), (4, 8192360)]) (.cons c89822_0 (.cons c89822_1 (.nil))) (by decide) (by decide))

theorem cover89823 : P.CoversSplit 26 10 89823 0xffff0000fffc0504ffff0000fffc050000000000000000000000000030300000050505050504050400000000000000000000000000000000000000000000000000000000330001000000000033000100000000003300010000000000300000000000000001000100000000000000000000000000010001000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 587, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89823_0 : P.sumLeaves 26 91978752 1016 = 114250005 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89823) (lo := 0) (len := 1016) (W := 114250005) check rows elimOK (by decide) (by decide) cover89823 (by decide)
  decide +kernel

theorem c89823_1 : P.sumLeaves 26 91979768 8 = 22929276 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89823) (lo := 1016) (len := 8) (W := 22929276) check rows elimOK (by decide) (by decide) cover89823 (by decide)
  decide +kernel

theorem h89823 : P.leaf 36 89823 = 137179281 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1016, 114250005), (8, 22929276)]) (.cons c89823_0 (.cons c89823_1 (.nil))) (by decide) (by decide))

theorem cover89829 : P.CoversSplit 26 10 89829 0xcc00cc00cc00c800cc00cc00cc00c80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 587, 922, 923, 972, 979, 1266, 1315]) (by decide +kernel)

theorem c89829_0 : P.sumLeaves 26 91984896 1024 = 3146904 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89829) (lo := 0) (len := 1024) (W := 3146904) check rows elimOK (by decide) (by decide) cover89829 (by decide)
  decide +kernel

theorem h89829 : P.leaf 36 89829 = 3146904 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3146904)]) (.cons c89829_0 (.nil)) (by decide) (by decide))

theorem cover89830 : P.CoversSplit 26 10 89830 0xcc00cc00cc00c800cc00cc00cc00c80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003300320000000000330030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 524, 587, 874, 922, 972, 979, 1266, 1315]) (by decide +kernel)

theorem c89830_0 : P.sumLeaves 26 91985920 1024 = 15411503 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89830) (lo := 0) (len := 1024) (W := 15411503) check rows elimOK (by decide) (by decide) cover89830 (by decide)
  decide +kernel

theorem h89830 : P.leaf 36 89830 = 15411503 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 15411503)]) (.cons c89830_0 (.nil)) (by decide) (by decide))

theorem cover89831 : P.CoversSplit 26 10 89831 0xcc00cc00cc00c800cc00cc00cc00c80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003300320000000000330030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 587, 922, 972, 979, 1266, 1315]) (by decide +kernel)

theorem c89831_0 : P.sumLeaves 26 91986944 1024 = 25516864 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89831) (lo := 0) (len := 1024) (W := 25516864) check rows elimOK (by decide) (by decide) cover89831 (by decide)
  decide +kernel

theorem h89831 : P.leaf 36 89831 = 25516864 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 25516864)]) (.cons c89831_0 (.nil)) (by decide) (by decide))

theorem cover89834 : P.CoversSplit 26 10 89834 0xf0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300030000000000030003000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 524, 874, 972, 979, 1266, 1665]) (by decide +kernel)

theorem c89834_0 : P.sumLeaves 26 91990016 1024 = 28594340 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89834) (lo := 0) (len := 1024) (W := 28594340) check rows elimOK (by decide) (by decide) cover89834 (by decide)
  decide +kernel

theorem h89834 : P.leaf 36 89834 = 28594340 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 28594340)]) (.cons c89834_0 (.nil)) (by decide) (by decide))

theorem cover89835 : P.CoversSplit 26 10 89835 0xf0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f000000000000000000000000030303000000000000000000000000000000000000000000000000000000000000000000000000000300030000000000030003000000000003000300000000000300030000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 587, 972, 979, 1266, 1322, 1658, 1665]) (by decide +kernel)

theorem c89835_0 : P.sumLeaves 26 91991040 1024 = 66533892 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89835) (lo := 0) (len := 1024) (W := 66533892) check rows elimOK (by decide) (by decide) cover89835 (by decide)
  decide +kernel

theorem h89835 : P.leaf 36 89835 = 66533892 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 66533892)]) (.cons c89835_0 (.nil)) (by decide) (by decide))

theorem cover89836 : P.CoversSplit 26 10 89836 0xfffffffffffcfaf8fffffffafffcfaf800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [524, 874, 922, 923, 972, 979, 1266, 1315]) (by decide +kernel)

theorem c89836_0 : P.sumLeaves 26 91992064 1008 = 8443944 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89836) (lo := 0) (len := 1008) (W := 8443944) check rows elimOK (by decide) (by decide) cover89836 (by decide)
  decide +kernel

theorem c89836_1 : P.sumLeaves 26 91993072 16 = 3718752 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89836) (lo := 1008) (len := 16) (W := 3718752) check rows elimOK (by decide) (by decide) cover89836 (by decide)
  decide +kernel

theorem h89836 : P.leaf 36 89836 = 12162696 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1008, 8443944), (16, 3718752)]) (.cons c89836_0 (.cons c89836_1 (.nil))) (by decide) (by decide))

theorem cover89837 : P.CoversSplit 26 10 89837 0xfffffffffffcfaf8fffffffafffcfaf800000000000000000000000030303000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 922, 923, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89837_0 : P.sumLeaves 26 91993088 1002 = 16336104 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89837) (lo := 0) (len := 1002) (W := 16336104) check rows elimOK (by decide) (by decide) cover89837 (by decide)
  decide +kernel

theorem c89837_1 : P.sumLeaves 26 91994090 22 = 7351616 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89837) (lo := 1002) (len := 22) (W := 7351616) check rows elimOK (by decide) (by decide) cover89837 (by decide)
  decide +kernel

theorem h89837 : P.leaf 36 89837 = 23687720 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1002, 16336104), (22, 7351616)]) (.cons c89837_0 (.cons c89837_1 (.nil))) (by decide) (by decide))

theorem cover89838 : P.CoversSplit 26 10 89838 0xfffffffffffcfaf8fffffffafffcfaf800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000330032000000000033003200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [524, 874, 922, 972, 979, 1266, 1315, 1665]) (by decide +kernel)

theorem c89838_0 : P.sumLeaves 26 91994112 994 = 48087297 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89838) (lo := 0) (len := 994) (W := 48087297) check rows elimOK (by decide) (by decide) cover89838 (by decide)
  decide +kernel

theorem c89838_1 : P.sumLeaves 26 91995106 30 = 35888600 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89838) (lo := 994) (len := 30) (W := 35888600) check rows elimOK (by decide) (by decide) cover89838 (by decide)
  decide +kernel

theorem h89838 : P.leaf 36 89838 = 83975897 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(994, 48087297), (30, 35888600)]) (.cons c89838_0 (.cons c89838_1 (.nil))) (by decide) (by decide))

theorem cover89839 : P.CoversSplit 26 10 89839 0xfffffffffffcfaf8fffffffafffcfaf800000000000000000000000030303000000000000000000000000000000000000000000000000000000000000000000000000000330032000000000033003200000000003300320000000000300030000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 922, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89839_0 : P.sumLeaves 26 91995136 975 = 70518694 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89839) (lo := 0) (len := 975) (W := 70518694) check rows elimOK (by decide) (by decide) cover89839 (by decide)
  decide +kernel

theorem c89839_1 : P.sumLeaves 26 91996111 49 = 74466197 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89839) (lo := 975) (len := 49) (W := 74466197) check rows elimOK (by decide) (by decide) cover89839 (by decide)
  decide +kernel

theorem h89839 : P.leaf 36 89839 = 144984891 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(975, 70518694), (49, 74466197)]) (.cons c89839_0 (.cons c89839_1 (.nil))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(89727, 120), (89812, 720), (89813, 720), (89814, 720), (89815, 720), (89818, 720), (89819, 720), (89820, 720), (89821, 720), (89822, 720), (89823, 720), (89829, 360), (89830, 720), (89831, 720), (89834, 720), (89835, 720), (89836, 720), (89837, 720), (89838, 720), (89839, 720)]

theorem segOK : checkSeg 20 perms 89727 89844 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 89727 89844 13440 557351554560 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 557351554560)
    (SegSum.cons (w := 120) h89727 (SegSum.cons (w := 720) h89812 (SegSum.cons (w := 720) h89813 (SegSum.cons (w := 720) h89814 (SegSum.cons (w := 720) h89815 (SegSum.cons (w := 720) h89818 (SegSum.cons (w := 720) h89819 (SegSum.cons (w := 720) h89820 (SegSum.cons (w := 720) h89821 (SegSum.cons (w := 720) h89822 (SegSum.cons (w := 720) h89823 (SegSum.cons (w := 360) h89829 (SegSum.cons (w := 720) h89830 (SegSum.cons (w := 720) h89831 (SegSum.cons (w := 720) h89834 (SegSum.cons (w := 720) h89835 (SegSum.cons (w := 720) h89836 (SegSum.cons (w := 720) h89837 (SegSum.cons (w := 720) h89838 (SegSum.cons (w := 720) h89839 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S68
