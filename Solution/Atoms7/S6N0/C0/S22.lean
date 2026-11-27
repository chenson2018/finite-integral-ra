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

namespace RACert.S6N0.C0.S22

open RACert RACert.Problem

theorem cover13119 : P.CoversSplit 26 10 13119 0xffff555000001010000000000000000033301110000010101100110000001000555550500000101055555050000010101110101000001010110010000000100033331110333310100000000000000000330011003300100011001100110010001111101011111010111110101111101011001000110010001100100011001000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 579, 873, 930, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c13119_0 : P.sumLeaves 26 13433856 696 = 320188 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13119) (lo := 0) (len := 696) (W := 320188) check rows elimOK (by decide) (by decide) cover13119 (by decide)
  decide +kernel

theorem c13119_1 : P.sumLeaves 26 13434552 328 = 767464 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13119) (lo := 696) (len := 328) (W := 767464) check rows elimOK (by decide) (by decide) cover13119 (by decide)
  decide +kernel

theorem h13119 : P.leaf 36 13119 = 1087652 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(696, 320188), (328, 767464)]) (.cons c13119_0 (.cons c13119_1 (.nil))) (by decide) (by decide))

theorem cover13168 : P.CoversSplit 26 10 13168 0xa0000000a0000000000000000000000000000000000000000000000000000000000050000000400000005000000040000000000000000000000000000000000000000000000000000000000000000000a00000008000000000000000000000000000000000000000000000000000000000005000000040000000500000004000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 873, 930, 972, 979, 1265, 1273, 1315, 1322, 1665]) (by decide +kernel)

theorem c13168_0 : P.sumLeaves 26 13484032 1024 = 1105 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13168) (lo := 0) (len := 1024) (W := 1105) check rows elimOK (by decide) (by decide) cover13168 (by decide)
  decide +kernel

theorem h13168 : P.leaf 36 13168 = 1105 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1105)]) (.cons c13168_0 (.nil)) (by decide) (by decide))

theorem cover13169 : P.CoversSplit 26 10 13169 0xa0000000a0000000000000000000000000000000000000000000000000000000000050000000400000005000000040000000000000000000000000000000000000000000000000000000000000000000a00000008000000000000000000000000000000000000000000000000000000000005000000040000000500000004000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 579, 873, 930, 972, 979, 1273, 1315, 1322, 1665]) (by decide +kernel)

theorem c13169_0 : P.sumLeaves 26 13485056 1024 = 17424 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13169) (lo := 0) (len := 1024) (W := 17424) check rows elimOK (by decide) (by decide) cover13169 (by decide)
  decide +kernel

theorem h13169 : P.leaf 36 13169 = 17424 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 17424)]) (.cons c13169_0 (.nil)) (by decide) (by decide))

theorem cover13170 : P.CoversSplit 26 10 13170 0xa0000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 579, 873, 879, 930, 972, 979, 1265, 1315]) (by decide +kernel)

theorem c13170_0 : P.sumLeaves 26 13486080 1024 = 16320 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13170) (lo := 0) (len := 1024) (W := 16320) check rows elimOK (by decide) (by decide) cover13170 (by decide)
  decide +kernel

theorem h13170 : P.leaf 36 13170 = 16320 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 16320)]) (.cons c13170_0 (.nil)) (by decide) (by decide))

theorem cover13171 : P.CoversSplit 26 10 13171 0xa0000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 579, 873, 930, 972, 979, 1273, 1315, 1665]) (by decide +kernel)

theorem c13171_0 : P.sumLeaves 26 13487104 1024 = 117664 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13171) (lo := 0) (len := 1024) (W := 117664) check rows elimOK (by decide) (by decide) cover13171 (by decide)
  decide +kernel

theorem h13171 : P.leaf 36 13171 = 117664 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 117664)]) (.cons c13171_0 (.nil)) (by decide) (by decide))

theorem cover13174 : P.CoversSplit 26 10 13174 0xff005500ff004000000000000000000000000000000000000000000000000000550050005500400055005000550040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 873, 879, 880, 930, 1265, 1315, 1322, 1658]) (by decide +kernel)

theorem c13174_0 : P.sumLeaves 26 13490176 1024 = 248416 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13174) (lo := 0) (len := 1024) (W := 248416) check rows elimOK (by decide) (by decide) cover13174 (by decide)
  decide +kernel

theorem h13174 : P.leaf 36 13174 = 248416 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 248416)]) (.cons c13174_0 (.nil)) (by decide) (by decide))

theorem cover13175 : P.CoversSplit 26 10 13175 0xff005500ff004000000000000000000000000000000000000000000000000000550050005500400055005000550040000000000000000000000000000000000000000000000000000000000000000000330011000000000011001100000000000000000000000000000000000000000011001000000000001100100000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 873, 930, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c13175_0 : P.sumLeaves 26 13491200 1024 = 855786 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13175) (lo := 0) (len := 1024) (W := 855786) check rows elimOK (by decide) (by decide) cover13175 (by decide)
  decide +kernel

theorem h13175 : P.leaf 36 13175 = 855786 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 855786)]) (.cons c13175_0 (.nil)) (by decide) (by decide))

theorem cover13177 : P.CoversSplit 26 10 13177 0xa0a00000a0a000000000000000000000a0a000008080000000000000000000000000505000004040000050500000404000005050000040400000500000004000a0a00000808000000000000000000000a00000008000000000000000000000000000505000004040000050500000404000005000000040000000500000004000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 579, 873, 930, 972, 979, 1273, 1315, 1322, 1665]) (by decide +kernel)

theorem c13177_0 : P.sumLeaves 26 13493248 1024 = 195080 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13177) (lo := 0) (len := 1024) (W := 195080) check rows elimOK (by decide) (by decide) cover13177 (by decide)
  decide +kernel

theorem h13177 : P.leaf 36 13177 = 195080 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 195080)]) (.cons c13177_0 (.nil)) (by decide) (by decide))

theorem cover13179 : P.CoversSplit 26 10 13179 0xa0a00000a0a000000000000000000000a0a000008080000000000000000000000000000000000000000000000000000000000000000000000000000000000000a0a00000808000000000000000000000a00000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 579, 873, 930, 972, 979, 1273, 1315, 1322]) (by decide +kernel)

theorem c13179_0 : P.sumLeaves 26 13495296 1024 = 2002260 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13179) (lo := 0) (len := 1024) (W := 2002260) check rows elimOK (by decide) (by decide) cover13179 (by decide)
  decide +kernel

theorem h13179 : P.leaf 36 13179 = 2002260 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2002260)]) (.cons c13179_0 (.nil)) (by decide) (by decide))

theorem cover13183 : P.CoversSplit 26 10 13183 0xffff5550ffff40400000000000000000fffc5550cccc404055005500440040005555505055554040555550505555404055545050444440405500500044004000ffff5550cccc40400000000000000000ff005500cc00400055005500440040005555505044444040555550504444404055005000440040005500500044004000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 873, 930, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c13183_0 : P.sumLeaves 26 13499392 492 = 2683692 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13183) (lo := 0) (len := 492) (W := 2683692) check rows elimOK (by decide) (by decide) cover13183 (by decide)
  decide +kernel

theorem c13183_1 : P.sumLeaves 26 13499884 334 = 4432326 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13183) (lo := 492) (len := 334) (W := 4432326) check rows elimOK (by decide) (by decide) cover13183 (by decide)
  decide +kernel

theorem c13183_2 : P.sumLeaves 26 13500218 198 = 10774020 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13183) (lo := 826) (len := 198) (W := 10774020) check rows elimOK (by decide) (by decide) cover13183 (by decide)
  decide +kernel

theorem h13183 : P.leaf 36 13183 = 17890038 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(492, 2683692), (334, 4432326), (198, 10774020)]) (.cons c13183_0 (.cons c13183_1 (.cons c13183_2 (.nil)))) (by decide) (by decide))

theorem cover13296 : P.CoversSplit 26 10 13296 0xf0000000f0000000f0000000f0000000000000000000000000000000000000000000fa000000c8000000aa00000088000000000000000000000000000000000000000000000000000000000000000000f0c00000c0c00000a080000080800000000000000000000000000000000000000000fac80000c8c80000aa8800008888 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 873, 930, 972, 979, 1265, 1273, 1322, 1658]) (by decide +kernel)

theorem c13296_0 : P.sumLeaves 26 13615104 1024 = 16699 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13296) (lo := 0) (len := 1024) (W := 16699) check rows elimOK (by decide) (by decide) cover13296 (by decide)
  decide +kernel

theorem h13296 : P.leaf 36 13296 = 16699 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 16699)]) (.cons c13296_0 (.nil)) (by decide) (by decide))

theorem cover13297 : P.CoversSplit 26 10 13297 0xf0000000f0000000f0000000f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f0c00000c0c00000a0800000808000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 872, 873, 930, 972, 979, 1273, 1658, 1665]) (by decide +kernel)

theorem c13297_0 : P.sumLeaves 26 13616128 1024 = 182272 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13297) (lo := 0) (len := 1024) (W := 182272) check rows elimOK (by decide) (by decide) cover13297 (by decide)
  decide +kernel

theorem h13297 : P.leaf 36 13297 = 182272 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 182272)]) (.cons c13297_0 (.nil)) (by decide) (by decide))

theorem cover13299 : P.CoversSplit 26 10 13299 0xf0000000f0000000f0000000f000000000000000000000000000000000000000000050000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000300000000000000020000000000000000000000000000000000000000000000000001000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 873, 930, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c13299_0 : P.sumLeaves 26 13618176 1024 = 604816 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13299) (lo := 0) (len := 1024) (W := 604816) check rows elimOK (by decide) (by decide) cover13299 (by decide)
  decide +kernel

theorem h13299 : P.leaf 36 13299 = 604816 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 604816)]) (.cons c13299_0 (.nil)) (by decide) (by decide))

theorem cover13302 : P.CoversSplit 26 10 13302 0xff00ff00ff00c800ff00aa00ff00880000000000000000000000000000000000ff00f000ff00c000aa00a000aa0080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 873, 879, 880, 930, 1265, 1315, 1322, 1658]) (by decide +kernel)

theorem c13302_0 : P.sumLeaves 26 13621248 1024 = 2069120 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13302) (lo := 0) (len := 1024) (W := 2069120) check rows elimOK (by decide) (by decide) cover13302 (by decide)
  decide +kernel

theorem h13302 : P.leaf 36 13302 = 2069120 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2069120)]) (.cons c13302_0 (.nil)) (by decide) (by decide))

theorem cover13303 : P.CoversSplit 26 10 13303 0xff00ff00ff00c800ff00aa00ff00880000000000000000000000000000000000ff00f000ff00c000aa00a000aa0080000000000000000000000000000000000000000000000000000000000000000000330033000000000022002200000000000000000000000000000000000000000033003000000000002200200000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 873, 930, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c13303_0 : P.sumLeaves 26 13622272 1017 = 10559291 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13303) (lo := 0) (len := 1017) (W := 10559291) check rows elimOK (by decide) (by decide) cover13303 (by decide)
  decide +kernel

theorem c13303_1 : P.sumLeaves 26 13623289 7 = 2256528 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13303) (lo := 1017) (len := 7) (W := 2256528) check rows elimOK (by decide) (by decide) cover13303 (by decide)
  decide +kernel

theorem h13303 : P.leaf 36 13303 = 12815819 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1017, 10559291), (7, 2256528)]) (.cons c13303_0 (.cons c13303_1 (.nil))) (by decide) (by decide))

theorem cover13311 : P.CoversSplit 26 10 13311 0xfffffffaffffc8c8ffffaaaaffff8888fffcfff8ccccc8c8aa88aa8888888888fffffafaffffc8c8aaaaaaaaaaaa8888fffcfaf8ccccc8c8aa88aa8888888888fffffffaccccc8c8ffffaaaacccc8888ffccffc8ccccc8c8aa88aa8888888888fffffafaccccc8c8aaaaaaaa88888888ffccfac8ccccc8c8aa88aa8888888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 930, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c13311_0 : P.sumLeaves 26 13630464 229 = 8006464 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13311) (lo := 0) (len := 229) (W := 8006464) check rows elimOK (by decide) (by decide) cover13311 (by decide)
  decide +kernel

theorem c13311_1 : P.sumLeaves 26 13630693 192 = 107783400 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13311) (lo := 229) (len := 192) (W := 107783400) check rows elimOK (by decide) (by decide) cover13311 (by decide)
  decide +kernel

theorem c13311_2 : P.sumLeaves 26 13630885 181 = 189325783 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13311) (lo := 421) (len := 181) (W := 189325783) check rows elimOK (by decide) (by decide) cover13311 (by decide)
  decide +kernel

theorem c13311_3 : P.sumLeaves 26 13631066 155 = 175971515 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13311) (lo := 602) (len := 155) (W := 175971515) check rows elimOK (by decide) (by decide) cover13311 (by decide)
  decide +kernel

theorem c13311_4 : P.sumLeaves 26 13631221 180 = 199421992 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13311) (lo := 757) (len := 180) (W := 199421992) check rows elimOK (by decide) (by decide) cover13311 (by decide)
  decide +kernel

theorem c13311_5 : P.sumLeaves 26 13631401 87 = 237189808 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13311) (lo := 937) (len := 87) (W := 237189808) check rows elimOK (by decide) (by decide) cover13311 (by decide)
  decide +kernel

theorem h13311 : P.leaf 36 13311 = 917698962 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(229, 8006464), (192, 107783400), (181, 189325783), (155, 175971515), (180, 199421992), (87, 237189808)]) (.cons c13311_0 (.cons c13311_1 (.cons c13311_2 (.cons c13311_3 (.cons c13311_4 (.cons c13311_5 (.nil))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(13119, 90), (13168, 180), (13169, 360), (13170, 360), (13171, 720), (13174, 180), (13175, 360), (13177, 180), (13179, 360), (13183, 180), (13296, 90), (13297, 360), (13299, 360), (13302, 180), (13303, 360), (13311, 90)]

theorem segOK : checkSeg 20 perms 13119 13526 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 13119 13526 4410 92387783790 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 92387783790)
    (SegSum.cons (w := 90) h13119 (SegSum.cons (w := 180) h13168 (SegSum.cons (w := 360) h13169 (SegSum.cons (w := 360) h13170 (SegSum.cons (w := 720) h13171 (SegSum.cons (w := 180) h13174 (SegSum.cons (w := 360) h13175 (SegSum.cons (w := 180) h13177 (SegSum.cons (w := 360) h13179 (SegSum.cons (w := 180) h13183 (SegSum.cons (w := 90) h13296 (SegSum.cons (w := 360) h13297 (SegSum.cons (w := 360) h13299 (SegSum.cons (w := 180) h13302 (SegSum.cons (w := 360) h13303 (SegSum.cons (w := 90) h13311 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))) (by decide)

end RACert.S6N0.C0.S22
