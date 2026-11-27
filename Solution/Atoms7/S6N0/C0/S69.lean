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

namespace RACert.S6N0.C0.S69

open RACert RACert.Problem

theorem cover89844 : P.CoversSplit 26 10 89844 0xcc00cc00cc00c800cc00cc00cc00c80000000000000000000000000000000000cc00c800cc00c800c000c000c000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 587, 874, 922, 923, 972, 979, 1315, 1658]) (by decide +kernel)

theorem c89844_0 : P.sumLeaves 26 92000256 1024 = 3056816 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89844) (lo := 0) (len := 1024) (W := 3056816) check rows elimOK (by decide) (by decide) cover89844 (by decide)
  decide +kernel

theorem h89844 : P.leaf 36 89844 = 3056816 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3056816)]) (.cons c89844_0 (.nil)) (by decide) (by decide))

theorem cover89845 : P.CoversSplit 26 10 89845 0xcc00cc00cc00c800cc00cc00cc00c80000000000000000000000000000000000cc00c800cc00c800c000c000c000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 587, 922, 923, 972, 979, 1315, 1658]) (by decide +kernel)

theorem c89845_0 : P.sumLeaves 26 92001280 1024 = 13162180 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89845) (lo := 0) (len := 1024) (W := 13162180) check rows elimOK (by decide) (by decide) cover89845 (by decide)
  decide +kernel

theorem h89845 : P.leaf 36 89845 = 13162180 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 13162180)]) (.cons c89845_0 (.nil)) (by decide) (by decide))

theorem cover89846 : P.CoversSplit 26 10 89846 0xcc00cc00cc00c800cc00cc00cc00c80000000000000000000000000000000000cc00c800cc00c800c000c000c000c0000000000000000000000000000000000000000000003300320000000000330030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 587, 874, 922, 972, 979, 1315, 1658]) (by decide +kernel)

theorem c89846_0 : P.sumLeaves 26 92002304 1024 = 36881367 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89846) (lo := 0) (len := 1024) (W := 36881367) check rows elimOK (by decide) (by decide) cover89846 (by decide)
  decide +kernel

theorem h89846 : P.leaf 36 89846 = 36881367 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 36881367)]) (.cons c89846_0 (.nil)) (by decide) (by decide))

theorem cover89847 : P.CoversSplit 26 10 89847 0xcc00cc00cc00c800cc00cc00cc00c80000000000000000000000000000000000cc00c800cc00c800c000c000c000c0000000000000000000000000000000000000000000003300320000000000330030000000000000000000000000000000000000000000330032000000000030003000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 587, 922, 972, 979, 1315, 1658]) (by decide +kernel)

theorem c89847_0 : P.sumLeaves 26 92003328 1024 = 61861781 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89847) (lo := 0) (len := 1024) (W := 61861781) check rows elimOK (by decide) (by decide) cover89847 (by decide)
  decide +kernel

theorem h89847 : P.leaf 36 89847 = 61861781 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 61861781)]) (.cons c89847_0 (.nil)) (by decide) (by decide))

theorem cover89850 : P.CoversSplit 26 10 89850 0xf0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f000000000000000000000000030303000000000000000000000005050000050500000000000000000000000000000100000000000300030000000000030003000000000003000300000000000300030000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 587, 874, 972, 979, 1322, 1658, 1665]) (by decide +kernel)

theorem c89850_0 : P.sumLeaves 26 92006400 1023 = 60219774 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89850) (lo := 0) (len := 1023) (W := 60219774) check rows elimOK (by decide) (by decide) cover89850 (by decide)
  decide +kernel

theorem c89850_1 : P.sumLeaves 26 92007423 1 = 1659592 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89850) (lo := 1023) (len := 1) (W := 1659592) check rows elimOK (by decide) (by decide) cover89850 (by decide)
  decide +kernel

theorem h89850 : P.leaf 36 89850 = 61879366 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1023, 60219774), (1, 1659592)]) (.cons c89850_0 (.cons c89850_1 (.nil))) (by decide) (by decide))

theorem cover89851 : P.CoversSplit 26 10 89851 0xf0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f000000000000000000000000030303000000000000000000000005050000050500000000000000000000000000000100000000000300030000000000030003000000000003000300000000000300030000000000000000000000000000000100000000000000000000000000000001000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 587, 972, 979, 1322, 1658, 1665]) (by decide +kernel)

theorem c89851_0 : P.sumLeaves 26 92007424 1021 = 125074869 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89851) (lo := 0) (len := 1021) (W := 125074869) check rows elimOK (by decide) (by decide) cover89851 (by decide)
  decide +kernel

theorem c89851_1 : P.sumLeaves 26 92008445 3 = 9475924 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89851) (lo := 1021) (len := 3) (W := 9475924) check rows elimOK (by decide) (by decide) cover89851 (by decide)
  decide +kernel

theorem h89851 : P.leaf 36 89851 = 134550793 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1021, 125074869), (3, 9475924)]) (.cons c89851_0 (.cons c89851_1 (.nil))) (by decide) (by decide))

theorem cover89852 : P.CoversSplit 26 10 89852 0xfffffffffffcfaf8fffffffafffcfaf800000000000000000000000030303000fffffafafffcfaf8f0f0f0f0f0f0f0f00000000000000000000000003030300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 874, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89852_0 : P.sumLeaves 26 92008448 797 = 11253952 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89852) (lo := 0) (len := 797) (W := 11253952) check rows elimOK (by decide) (by decide) cover89852 (by decide)
  decide +kernel

theorem c89852_1 : P.sumLeaves 26 92009245 210 = 31665024 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89852) (lo := 797) (len := 210) (W := 31665024) check rows elimOK (by decide) (by decide) cover89852 (by decide)
  decide +kernel

theorem c89852_2 : P.sumLeaves 26 92009455 17 = 11439600 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89852) (lo := 1007) (len := 17) (W := 11439600) check rows elimOK (by decide) (by decide) cover89852 (by decide)
  decide +kernel

theorem h89852 : P.leaf 36 89852 = 54358576 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(797, 11253952), (210, 31665024), (17, 11439600)]) (.cons c89852_0 (.cons c89852_1 (.cons c89852_2 (.nil)))) (by decide) (by decide))

theorem cover89853 : P.CoversSplit 26 10 89853 0xfffffffffffcfaf8fffffffafffcfaf800000000000000000000000030303000fffffafafffcfaf8f0f0f0f0f0f0f0f00000000000000000000000003030300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89853_0 : P.sumLeaves 26 92009472 797 = 22287590 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89853) (lo := 0) (len := 797) (W := 22287590) check rows elimOK (by decide) (by decide) cover89853 (by decide)
  decide +kernel

theorem c89853_1 : P.sumLeaves 26 92010269 210 = 61576732 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89853) (lo := 797) (len := 210) (W := 61576732) check rows elimOK (by decide) (by decide) cover89853 (by decide)
  decide +kernel

theorem c89853_2 : P.sumLeaves 26 92010479 17 = 16307040 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89853) (lo := 1007) (len := 17) (W := 16307040) check rows elimOK (by decide) (by decide) cover89853 (by decide)
  decide +kernel

theorem h89853 : P.leaf 36 89853 = 100171362 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(797, 22287590), (210, 61576732), (17, 16307040)]) (.cons c89853_0 (.cons c89853_1 (.cons c89853_2 (.nil)))) (by decide) (by decide))

theorem cover89854 : P.CoversSplit 26 10 89854 0xfffffffffffcfaf8fffffffafffcfaf800000000000000000000000030303000fffffafafffcfaf8f0f0f0f0f0f0f0f00000000000000000000000003030300000000000330032000000000033003200000000003300320000000000300030000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 874, 922, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89854_0 : P.sumLeaves 26 92010496 748 = 36312054 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89854) (lo := 0) (len := 748) (W := 36312054) check rows elimOK (by decide) (by decide) cover89854 (by decide)
  decide +kernel

theorem c89854_1 : P.sumLeaves 26 92011244 234 = 106968693 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89854) (lo := 748) (len := 234) (W := 106968693) check rows elimOK (by decide) (by decide) cover89854 (by decide)
  decide +kernel

theorem c89854_2 : P.sumLeaves 26 92011478 42 = 81451732 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89854) (lo := 982) (len := 42) (W := 81451732) check rows elimOK (by decide) (by decide) cover89854 (by decide)
  decide +kernel

theorem h89854 : P.leaf 36 89854 = 224732479 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(748, 36312054), (234, 106968693), (42, 81451732)]) (.cons c89854_0 (.cons c89854_1 (.cons c89854_2 (.nil)))) (by decide) (by decide))

theorem cover89855 : P.CoversSplit 26 10 89855 0xfffffffffffcfaf8fffffffafffcfaf800000000000000000000000030303000fffffafafffcfaf8f0f0f0f0f0f0f0f00000000000000000000000003030300000000000330032000000000033003200000000003300320000000000300030000000000033003200000000003000300000000000330032000000000030003000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 922, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89855_0 : P.sumLeaves 26 92011520 722 = 49198803 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89855) (lo := 0) (len := 722) (W := 49198803) check rows elimOK (by decide) (by decide) cover89855 (by decide)
  decide +kernel

theorem c89855_1 : P.sumLeaves 26 92012242 231 = 133467796 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89855) (lo := 722) (len := 231) (W := 133467796) check rows elimOK (by decide) (by decide) cover89855 (by decide)
  decide +kernel

theorem c89855_2 : P.sumLeaves 26 92012473 71 = 163232519 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89855) (lo := 953) (len := 71) (W := 163232519) check rows elimOK (by decide) (by decide) cover89855 (by decide)
  decide +kernel

theorem h89855 : P.leaf 36 89855 = 345899118 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(722, 49198803), (231, 133467796), (71, 163232519)]) (.cons c89855_0 (.cons c89855_1 (.cons c89855_2 (.nil)))) (by decide) (by decide))

theorem cover90021 : P.CoversSplit 26 10 90021 0xcc00cc0000000000cc00cc0000000000cc00cc0000000000c800c80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 536, 538, 922, 923, 972, 979, 1272, 1658]) (by decide +kernel)

theorem c90021_0 : P.sumLeaves 26 92181504 1024 = 34703072 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90021) (lo := 0) (len := 1024) (W := 34703072) check rows elimOK (by decide) (by decide) cover90021 (by decide)
  decide +kernel

theorem h90021 : P.leaf 36 90021 = 34703072 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 34703072)]) (.cons c90021_0 (.nil)) (by decide) (by decide))

theorem cover90023 : P.CoversSplit 26 10 90023 0xcc00cc0000000000cc00cc0000000000cc00cc0000000000c800c80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 922, 972, 979, 1272, 1315, 1322, 1658]) (by decide +kernel)

theorem c90023_0 : P.sumLeaves 26 92183552 1024 = 57540284 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90023) (lo := 0) (len := 1024) (W := 57540284) check rows elimOK (by decide) (by decide) cover90023 (by decide)
  decide +kernel

theorem h90023 : P.leaf 36 90023 = 57540284 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 57540284)]) (.cons c90023_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(89844, 720), (89845, 720), (89846, 720), (89847, 720), (89850, 720), (89851, 720), (89852, 720), (89853, 720), (89854, 720), (89855, 720), (90021, 360), (90023, 360)]

theorem segOK : checkSeg 20 perms 89844 90024 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 89844 90024 7920 779526371520 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 779526371520)
    (SegSum.cons (w := 720) h89844 (SegSum.cons (w := 720) h89845 (SegSum.cons (w := 720) h89846 (SegSum.cons (w := 720) h89847 (SegSum.cons (w := 720) h89850 (SegSum.cons (w := 720) h89851 (SegSum.cons (w := 720) h89852 (SegSum.cons (w := 720) h89853 (SegSum.cons (w := 720) h89854 (SegSum.cons (w := 720) h89855 (SegSum.cons (w := 360) h90021 (SegSum.cons (w := 360) h90023 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))) (by decide)

end RACert.S6N0.C0.S69
