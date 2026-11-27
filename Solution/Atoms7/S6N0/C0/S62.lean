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

namespace RACert.S6N0.C0.S62

open RACert RACert.Problem

theorem cover88788 : P.CoversSplit 26 10 88788 0xcc000000cc000400cc000000cc00040000000000000000000000000000000000040004000400040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 559, 587, 874, 922, 923, 972, 979, 1315]) (by decide +kernel)

theorem c88788_0 : P.sumLeaves 26 90918912 1024 = 160032 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88788) (lo := 0) (len := 1024) (W := 160032) check rows elimOK (by decide) (by decide) cover88788 (by decide)
  decide +kernel

theorem h88788 : P.leaf 36 88788 = 160032 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 160032)]) (.cons c88788_0 (.nil)) (by decide) (by decide))

theorem cover88789 : P.CoversSplit 26 10 88789 0xcc000000cc000400cc000000cc00040000000000000000000000000000000000040004000400040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 559, 587, 922, 923, 972, 979, 1315]) (by decide +kernel)

theorem c88789_0 : P.sumLeaves 26 90919936 1024 = 1329464 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88789) (lo := 0) (len := 1024) (W := 1329464) check rows elimOK (by decide) (by decide) cover88789 (by decide)
  decide +kernel

theorem h88789 : P.leaf 36 88789 = 1329464 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1329464)]) (.cons c88789_0 (.nil)) (by decide) (by decide))

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

theorem c88796_0 : P.sumLeaves 26 90927104 1024 = 3802034 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88796) (lo := 0) (len := 1024) (W := 3802034) check rows elimOK (by decide) (by decide) cover88796 (by decide)
  decide +kernel

theorem h88796 : P.leaf 36 88796 = 3802034 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3802034)]) (.cons c88796_0 (.nil)) (by decide) (by decide))

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

theorem c88806_0 : P.sumLeaves 26 90937344 1024 = 1660972 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88806) (lo := 0) (len := 1024) (W := 1660972) check rows elimOK (by decide) (by decide) cover88806 (by decide)
  decide +kernel

theorem h88806 : P.leaf 36 88806 = 1660972 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1660972)]) (.cons c88806_0 (.nil)) (by decide) (by decide))

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

theorem c88810_0 : P.sumLeaves 26 90941440 1024 = 1566008 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88810) (lo := 0) (len := 1024) (W := 1566008) check rows elimOK (by decide) (by decide) cover88810 (by decide)
  decide +kernel

theorem h88810 : P.leaf 36 88810 = 1566008 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1566008)]) (.cons c88810_0 (.nil)) (by decide) (by decide))

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

theorem c88814_0 : P.sumLeaves 26 90945536 994 = 4191059 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88814) (lo := 0) (len := 994) (W := 4191059) check rows elimOK (by decide) (by decide) cover88814 (by decide)
  decide +kernel

theorem c88814_1 : P.sumLeaves 26 90946530 30 = 3200668 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88814) (lo := 994) (len := 30) (W := 3200668) check rows elimOK (by decide) (by decide) cover88814 (by decide)
  decide +kernel

theorem h88814 : P.leaf 36 88814 = 7391727 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(994, 4191059), (30, 3200668)]) (.cons c88814_0 (.cons c88814_1 (.nil))) (by decide) (by decide))

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

theorem c88823_0 : P.sumLeaves 26 90954752 1024 = 25627797 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88823) (lo := 0) (len := 1024) (W := 25627797) check rows elimOK (by decide) (by decide) cover88823 (by decide)
  decide +kernel

theorem h88823 : P.leaf 36 88823 = 25627797 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 25627797)]) (.cons c88823_0 (.nil)) (by decide) (by decide))

theorem cover88825 : P.CoversSplit 26 10 88825 0xf0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f000000000000000000000000030303000000000000000000000005050000050500000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 587, 922, 923, 972, 979, 1322, 1658, 1665]) (by decide +kernel)

theorem c88825_0 : P.sumLeaves 26 90956800 1024 = 6999652 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88825) (lo := 0) (len := 1024) (W := 6999652) check rows elimOK (by decide) (by decide) cover88825 (by decide)
  decide +kernel

theorem h88825 : P.leaf 36 88825 = 6999652 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6999652)]) (.cons c88825_0 (.nil)) (by decide) (by decide))

theorem cover88826 : P.CoversSplit 26 10 88826 0xf0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f000000000000000000000000030303000000000000000000000005050000050500000000000000000000000000000100000000000300030000000000030003000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 587, 874, 972, 979, 1273, 1322, 1658, 1665]) (by decide +kernel)

theorem c88826_0 : P.sumLeaves 26 90957824 1024 = 11696534 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88826) (lo := 0) (len := 1024) (W := 11696534) check rows elimOK (by decide) (by decide) cover88826 (by decide)
  decide +kernel

theorem h88826 : P.leaf 36 88826 = 11696534 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 11696534)]) (.cons c88826_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(88788, 360), (88789, 720), (88790, 720), (88791, 720), (88793, 360), (88794, 720), (88795, 720), (88796, 720), (88797, 720), (88798, 720), (88799, 720), (88806, 720), (88807, 720), (88810, 720), (88811, 720), (88814, 720), (88815, 720), (88820, 360), (88821, 720), (88822, 720), (88823, 720), (88825, 360), (88826, 720)]

theorem segOK : checkSeg 20 perms 88788 88827 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 88788 88827 15120 153003712320 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 153003712320)
    (SegSum.cons (w := 360) h88788 (SegSum.cons (w := 720) h88789 (SegSum.cons (w := 720) h88790 (SegSum.cons (w := 720) h88791 (SegSum.cons (w := 360) h88793 (SegSum.cons (w := 720) h88794 (SegSum.cons (w := 720) h88795 (SegSum.cons (w := 720) h88796 (SegSum.cons (w := 720) h88797 (SegSum.cons (w := 720) h88798 (SegSum.cons (w := 720) h88799 (SegSum.cons (w := 720) h88806 (SegSum.cons (w := 720) h88807 (SegSum.cons (w := 720) h88810 (SegSum.cons (w := 720) h88811 (SegSum.cons (w := 720) h88814 (SegSum.cons (w := 720) h88815 (SegSum.cons (w := 360) h88820 (SegSum.cons (w := 720) h88821 (SegSum.cons (w := 720) h88822 (SegSum.cons (w := 720) h88823 (SegSum.cons (w := 360) h88825 (SegSum.cons (w := 720) h88826 (show SegSum (P.leaf 36) [] 0 from rfl)))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S62
