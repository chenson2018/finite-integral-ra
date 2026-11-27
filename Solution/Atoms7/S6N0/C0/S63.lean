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

namespace RACert.S6N0.C0.S63

open RACert RACert.Problem

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

theorem c88828_0 : P.sumLeaves 26 90959872 797 = 1798806 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88828) (lo := 0) (len := 797) (W := 1798806) check rows elimOK (by decide) (by decide) cover88828 (by decide)
  decide +kernel

theorem c88828_1 : P.sumLeaves 26 90960669 210 = 4957172 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88828) (lo := 797) (len := 210) (W := 4957172) check rows elimOK (by decide) (by decide) cover88828 (by decide)
  decide +kernel

theorem c88828_2 : P.sumLeaves 26 90960879 17 = 2220176 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88828) (lo := 1007) (len := 17) (W := 2220176) check rows elimOK (by decide) (by decide) cover88828 (by decide)
  decide +kernel

theorem h88828 : P.leaf 36 88828 = 8976154 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(797, 1798806), (210, 4957172), (17, 2220176)]) (.cons c88828_0 (.cons c88828_1 (.cons c88828_2 (.nil)))) (by decide) (by decide))

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

theorem c88831_0 : P.sumLeaves 26 90962944 748 = 22860820 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88831) (lo := 0) (len := 748) (W := 22860820) check rows elimOK (by decide) (by decide) cover88831 (by decide)
  decide +kernel

theorem c88831_1 : P.sumLeaves 26 90963692 234 = 62609299 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88831) (lo := 748) (len := 234) (W := 62609299) check rows elimOK (by decide) (by decide) cover88831 (by decide)
  decide +kernel

theorem c88831_2 : P.sumLeaves 26 90963926 42 = 43237914 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88831) (lo := 982) (len := 42) (W := 43237914) check rows elimOK (by decide) (by decide) cover88831 (by decide)
  decide +kernel

theorem h88831 : P.leaf 36 88831 = 128708033 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(748, 22860820), (234, 62609299), (42, 43237914)]) (.cons c88831_0 (.cons c88831_1 (.cons c88831_2 (.nil)))) (by decide) (by decide))

theorem cover88979 : P.CoversSplit 26 10 88979 0x8000000000000000800000000000000080000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 530, 538, 608, 615, 972, 979, 1315]) (by decide +kernel)

theorem c88979_0 : P.sumLeaves 26 91114496 1024 = 1205480 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88979) (lo := 0) (len := 1024) (W := 1205480) check rows elimOK (by decide) (by decide) cover88979 (by decide)
  decide +kernel

theorem h88979 : P.leaf 36 88979 = 1205480 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1205480)]) (.cons c88979_0 (.nil)) (by decide) (by decide))

theorem cover88981 : P.CoversSplit 26 10 88981 0xcc00000000000000cc00000000000000cc00000000000003c8000000000000000c000c000000000000000000000000000c000c0000000003000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 922, 923, 972, 979, 1315, 1322, 1658]) (by decide +kernel)

theorem c88981_0 : P.sumLeaves 26 91116544 1024 = 687608 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88981) (lo := 0) (len := 1024) (W := 687608) check rows elimOK (by decide) (by decide) cover88981 (by decide)
  decide +kernel

theorem h88981 : P.leaf 36 88981 = 687608 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 687608)]) (.cons c88981_0 (.nil)) (by decide) (by decide))

theorem cover88983 : P.CoversSplit 26 10 88983 0xcc00000000000000cc00000000000000cc00000000000003c8000000000000000c000c000000000008000000000000000c000c0000000003080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 922, 972, 979, 1315, 1322, 1658]) (by decide +kernel)

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

theorem c88986_0 : P.sumLeaves 26 91121664 1024 = 743296 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88986) (lo := 0) (len := 1024) (W := 743296) check rows elimOK (by decide) (by decide) cover88986 (by decide)
  decide +kernel

theorem h88986 : P.leaf 36 88986 = 743296 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 743296)]) (.cons c88986_0 (.nil)) (by decide) (by decide))

theorem cover88987 : P.CoversSplit 26 10 88987 0xa0a0000000000000a0a0000000000000a0a0000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 538, 615, 972, 1315, 1322]) (by decide +kernel)

theorem c88987_0 : P.sumLeaves 26 91122688 1024 = 8369676 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88987) (lo := 0) (len := 1024) (W := 8369676) check rows elimOK (by decide) (by decide) cover88987 (by decide)
  decide +kernel

theorem h88987 : P.leaf 36 88987 = 8369676 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8369676)]) (.cons c88987_0 (.nil)) (by decide) (by decide))

theorem cover88988 : P.CoversSplit 26 10 88988 0xffff000000000000ffff000000000000ffff00000000000cfafa0000000000080f0f0f0f0000000000000000000000000f0f0f0f0000000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 874, 922, 923, 979, 1315, 1322, 1658]) (by decide +kernel)

theorem c88988_0 : P.sumLeaves 26 91123712 1023 = 899936 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88988) (lo := 0) (len := 1023) (W := 899936) check rows elimOK (by decide) (by decide) cover88988 (by decide)
  decide +kernel

theorem c88988_1 : P.sumLeaves 26 91124735 1 = 24192 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88988) (lo := 1023) (len := 1) (W := 24192) check rows elimOK (by decide) (by decide) cover88988 (by decide)
  decide +kernel

theorem h88988 : P.leaf 36 88988 = 924128 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1023, 899936), (1, 24192)]) (.cons c88988_0 (.cons c88988_1 (.nil))) (by decide) (by decide))

theorem cover88989 : P.CoversSplit 26 10 88989 0xffff000000000000ffff000000000000ffff00000000000cfafa0000000000080f0f0f0f0000000000000000000000000f0f0f0f0000000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 922, 923, 979, 1315, 1322, 1658]) (by decide +kernel)

theorem c88989_0 : P.sumLeaves 26 91124736 1023 = 5390308 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88989) (lo := 0) (len := 1023) (W := 5390308) check rows elimOK (by decide) (by decide) cover88989 (by decide)
  decide +kernel

theorem c88989_1 : P.sumLeaves 26 91125759 1 = 125688 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88989) (lo := 1023) (len := 1) (W := 125688) check rows elimOK (by decide) (by decide) cover88989 (by decide)
  decide +kernel

theorem h88989 : P.leaf 36 88989 = 5515996 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1023, 5390308), (1, 125688)]) (.cons c88989_0 (.cons c88989_1 (.nil))) (by decide) (by decide))

theorem cover88990 : P.CoversSplit 26 10 88990 0xffff000000000000ffff000000000000ffff00000000000cfafa0000000000080f0f0f0f000000000a0a0a0a000000000f0f0f0f0000000c0a0a0a0a000000080000000000000000000000000000000000ff000000cc000c00fa000000c800080000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 874, 922, 979, 1315, 1322, 1658]) (by decide +kernel)

theorem c88990_0 : P.sumLeaves 26 91125760 886 = 3050964 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88990) (lo := 0) (len := 886) (W := 3050964) check rows elimOK (by decide) (by decide) cover88990 (by decide)
  decide +kernel

theorem c88990_1 : P.sumLeaves 26 91126646 138 = 9864616 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88990) (lo := 886) (len := 138) (W := 9864616) check rows elimOK (by decide) (by decide) cover88990 (by decide)
  decide +kernel

theorem h88990 : P.leaf 36 88990 = 12915580 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(886, 3050964), (138, 9864616)]) (.cons c88990_0 (.cons c88990_1 (.nil))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(88827, 720), (88828, 720), (88829, 720), (88830, 720), (88831, 720), (88979, 360), (88981, 720), (88983, 720), (88985, 720), (88986, 720), (88987, 720), (88988, 720), (88989, 720), (88990, 720)]

theorem segOK : checkSeg 20 perms 88827 88991 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 88827 88991 9720 217586147040 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 217586147040)
    (SegSum.cons (w := 720) h88827 (SegSum.cons (w := 720) h88828 (SegSum.cons (w := 720) h88829 (SegSum.cons (w := 720) h88830 (SegSum.cons (w := 720) h88831 (SegSum.cons (w := 360) h88979 (SegSum.cons (w := 720) h88981 (SegSum.cons (w := 720) h88983 (SegSum.cons (w := 720) h88985 (SegSum.cons (w := 720) h88986 (SegSum.cons (w := 720) h88987 (SegSum.cons (w := 720) h88988 (SegSum.cons (w := 720) h88989 (SegSum.cons (w := 720) h88990 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))) (by decide)

end RACert.S6N0.C0.S63
