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

namespace RACert.S4N1.C0.S17

open RACert RACert.Problem

theorem cover2013 : P.CoversSplit 24 10 2013 0xff00ff0000000000ff33ff3300000000ff00ff0000000000ff00ff00000000000000000000000000000000000000000000000000000000000000000000000000ff00ff0000000000ff33ff3300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 516, 860, 872, 915, 1258, 1308]) (ps := [(14, [923], [915])]) (by decide +kernel)

theorem c2013_0 : P.sumLeaves 24 2061312 1000 = 6356604 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 2013) (lo := 0) (len := 1000) (W := 6356604) check rows elimOK (by decide) (by decide) cover2013 (by decide)
  decide +kernel

theorem c2013_1 : P.sumLeaves 24 2062312 24 = 5000600 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 2013) (lo := 1000) (len := 24) (W := 5000600) check rows elimOK (by decide) (by decide) cover2013 (by decide)
  decide +kernel

theorem h2013 : P.leaf 34 2013 = 11357204 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1000, 6356604), (24, 5000600)]) (.cons c2013_0 (.cons c2013_1 (.nil))) (by decide) (by decide))

theorem cover2014 : P.CoversSplit 24 10 2014 0xffffffffa0a0a0a0ffffffffa0a0a0a0a0a0a5a500000000a0a0a5a500000000ffccffcc80008000cc00cc0080008000a080a584000000008000840000000000ffffffffa0a0a0a0ffffffffa0a0a0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 516, 860, 867, 915, 916, 1202, 1258, 1259, 1308]) (by decide +kernel)

theorem c2014_0 : P.sumLeaves 24 2062336 686 = 3383075 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 2014) (lo := 0) (len := 686) (W := 3383075) check rows elimOK (by decide) (by decide) cover2014 (by decide)
  decide +kernel

theorem c2014_1 : P.sumLeaves 24 2063022 279 = 8679098 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 2014) (lo := 686) (len := 279) (W := 8679098) check rows elimOK (by decide) (by decide) cover2014 (by decide)
  decide +kernel

theorem c2014_2 : P.sumLeaves 24 2063301 59 = 9249360 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 2014) (lo := 965) (len := 59) (W := 9249360) check rows elimOK (by decide) (by decide) cover2014 (by decide)
  decide +kernel

theorem h2014 : P.leaf 34 2014 = 21311533 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(686, 3383075), (279, 8679098), (59, 9249360)]) (.cons c2014_0 (.cons c2014_1 (.cons c2014_2 (.nil)))) (by decide) (by decide))

theorem cover2015 : P.CoversSplit 24 10 2015 0xffffffffa0a0a0a0ffffffffa0a0a0a0ffffffff0000a0a0ffffffff0000a0a0ffccffcc80008000cc00cc0080008000ffccffcc00008000cc00cc0000008000ffffffffa0a0a0a0ffffffffa0a0a0a000000000000000000000000000000000ffccffcc80008000cc00cc008000800000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [516, 860, 915, 916, 1202, 1217, 1258, 1259, 1308]) (by decide +kernel)

theorem c2015_0 : P.sumLeaves 24 2063360 492 = 9143964 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 2015) (lo := 0) (len := 492) (W := 9143964) check rows elimOK (by decide) (by decide) cover2015 (by decide)
  decide +kernel

theorem c2015_1 : P.sumLeaves 24 2063852 310 = 20725818 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 2015) (lo := 492) (len := 310) (W := 20725818) check rows elimOK (by decide) (by decide) cover2015 (by decide)
  decide +kernel

theorem c2015_2 : P.sumLeaves 24 2064162 148 = 15821283 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 2015) (lo := 802) (len := 148) (W := 15821283) check rows elimOK (by decide) (by decide) cover2015 (by decide)
  decide +kernel

theorem c2015_3 : P.sumLeaves 24 2064310 74 = 35833462 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 2015) (lo := 950) (len := 74) (W := 35833462) check rows elimOK (by decide) (by decide) cover2015 (by decide)
  decide +kernel

theorem h2015 : P.leaf 34 2015 = 81524527 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(492, 9143964), (310, 20725818), (148, 15821283), (74, 35833462)]) (.cons c2015_0 (.cons c2015_1 (.cons c2015_2 (.cons c2015_3 (.nil))))) (by decide) (by decide))

theorem cover2028 : P.CoversSplit 24 10 2028 0x8800000000000000000000000000000080000000000000000000000000000000000000000000000000220000000000000000000000000000002000000000000088000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 522, 860, 872, 915, 1209, 1259]) (by decide +kernel)

theorem c2028_0 : P.sumLeaves 24 2076672 1024 = 736882 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 2028) (lo := 0) (len := 1024) (W := 736882) check rows elimOK (by decide) (by decide) cover2028 (by decide)
  decide +kernel

theorem h2028 : P.leaf 34 2028 = 736882 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 736882)]) (.cons c2028_0 (.nil)) (by decide) (by decide))

theorem cover2029 : P.CoversSplit 24 10 2029 0xcc000000000000000000000000000000cc0000000000000000000000000000000000000000000000003300000000000000000000000000000033000000000000cc000000000000000000000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 860, 872, 915, 1209, 1251, 1609]) (by decide +kernel)

theorem c2029_0 : P.sumLeaves 24 2077696 1024 = 6686356 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 2029) (lo := 0) (len := 1024) (W := 6686356) check rows elimOK (by decide) (by decide) cover2029 (by decide)
  decide +kernel

theorem h2029 : P.leaf 34 2029 = 6686356 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6686356)]) (.cons c2029_0 (.nil)) (by decide) (by decide))

theorem cover2030 : P.CoversSplit 24 10 2030 0xaaaa0000000000000000000000000000a0a000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000aaaa0000000000000000000000000000a0a000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 522, 860, 872, 916, 1209, 1258, 1259]) (by decide +kernel)

theorem c2030_0 : P.sumLeaves 24 2078720 1024 = 7664050 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 2030) (lo := 0) (len := 1024) (W := 7664050) check rows elimOK (by decide) (by decide) cover2030 (by decide)
  decide +kernel

theorem h2030 : P.leaf 34 2030 = 7664050 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 7664050)]) (.cons c2030_0 (.nil)) (by decide) (by decide))

theorem cover2031 : P.CoversSplit 24 10 2031 0xffff0000000000000000000000000000ffff00000000000000330000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000ffff00000000000000330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 860, 916, 1202, 1209, 1251, 1258, 1259]) (by decide +kernel)

theorem c2031_0 : P.sumLeaves 24 2079744 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 2031) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover2031 (by decide)
  decide +kernel

theorem contract2031_1 : P.leaf 30 32500 = 6336 := by
  apply (leaf_contract (k := 30) (b := 16) (H := 32500) (ss := [(12, 1, 867), (30, 1, 1251), (31, 1, 1209), (16, 0, 1258), (4, 1, 566), (27, 0, 1258), (17, 0, 1259), (29, 0, 1259), (13, 1, 1265), (14, 1, 1266), (15, 1, 1273), (8, 7, 1314), (7, 1, 1315), (9, 1, 1322)]) (ids := [0, 1, 3, 4, 8, 9, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26]) (cs := [2, 3, 1, 4, 5, 1, 1, 1, 6, 7, 1, 1, 1, 1, 0, 0, 8, 9, 10, 11, 12, 13, 14, 15, 16, 0, 17, 0, 1, 1]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c2031_1 : P.sumLeaves 24 2080000 64 = 6336 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 32500) rows (by decide) (by decide)).symm.trans contract2031_1

theorem c2031_2 : P.sumLeaves 24 2080064 448 = 8510006 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 2031) (lo := 320) (len := 448) (W := 8510006) check rows elimOK (by decide) (by decide) cover2031 (by decide)
  decide +kernel

theorem contract2031_3 : P.leaf 30 32508 = 12198 := by
  apply (leaf_contract (k := 30) (b := 16) (H := 32508) (ss := [(12, 1, 867), (30, 1, 1251), (31, 1, 1209), (16, 0, 1258), (4, 1, 529), (27, 0, 1258), (17, 0, 1259), (29, 0, 1259), (13, 1, 1265), (14, 1, 1266), (15, 1, 1273), (8, 7, 1314), (7, 1, 1315), (9, 1, 1322)]) (ids := [0, 1, 3, 4, 8, 9, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26]) (cs := [2, 3, 1, 4, 5, 1, 1, 1, 6, 7, 1, 1, 1, 1, 0, 0, 8, 9, 10, 11, 12, 13, 14, 15, 16, 0, 17, 0, 1, 1]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c2031_3 : P.sumLeaves 24 2080512 64 = 12198 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 32508) rows (by decide) (by decide)).symm.trans contract2031_3

theorem c2031_4 : P.sumLeaves 24 2080576 192 = 25669936 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 2031) (lo := 832) (len := 192) (W := 25669936) check rows elimOK (by decide) (by decide) cover2031 (by decide)
  decide +kernel

theorem h2031 : P.leaf 34 2031 = 34198476 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 6336), (448, 8510006), (64, 12198), (192, 25669936)]) (.cons c2031_0 (.cons c2031_1 (.cons c2031_2 (.cons c2031_3 (.cons c2031_4 (.nil)))))) (by decide) (by decide))

theorem cover2046 : P.CoversSplit 24 10 2046 0xffffffffaaaaaaaaffffffffaaaaaaaaf5f5f5f505050000f5f5f5f505050000ffccffcc88888888cccccccc88888888f5c4f5c400000000c4c4c4c400000000ffffffffaaaaaaaaffffffffaaaaaaaaf5f5f5f500000000f5f5f5f5000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 860, 867, 915, 916, 1202, 1209, 1217, 1258]) (by decide +kernel)

theorem c2046_0 : P.sumLeaves 24 2095104 449 = 8523133 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 2046) (lo := 0) (len := 449) (W := 8523133) check rows elimOK (by decide) (by decide) cover2046 (by decide)
  decide +kernel

theorem c2046_1 : P.sumLeaves 24 2095553 245 = 11939335 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 2046) (lo := 449) (len := 245) (W := 11939335) check rows elimOK (by decide) (by decide) cover2046 (by decide)
  decide +kernel

theorem c2046_2 : P.sumLeaves 24 2095798 207 = 15639832 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 2046) (lo := 694) (len := 207) (W := 15639832) check rows elimOK (by decide) (by decide) cover2046 (by decide)
  decide +kernel

theorem c2046_3 : P.sumLeaves 24 2096005 123 = 40194684 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 2046) (lo := 901) (len := 123) (W := 40194684) check rows elimOK (by decide) (by decide) cover2046 (by decide)
  decide +kernel

theorem h2046 : P.leaf 34 2046 = 76296984 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(449, 8523133), (245, 11939335), (207, 15639832), (123, 40194684)]) (.cons c2046_0 (.cons c2046_1 (.cons c2046_2 (.cons c2046_3 (.nil))))) (by decide) (by decide))

theorem cover2047 : P.CoversSplit 24 10 2047 0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffccffcc88888888cccccccc88888888ffccffcc88888888cccccccc88888888ffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffccffcc88888888cccccccc88888888ffccffcc88888888cccccccc88888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [860, 915, 916, 1202, 1258]) (by decide +kernel)

theorem c2047_0 : P.sumLeaves 24 2096128 236 = 18506832 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 2047) (lo := 0) (len := 236) (W := 18506832) check rows elimOK (by decide) (by decide) cover2047 (by decide)
  decide +kernel

theorem c2047_1 : P.sumLeaves 24 2096364 132 = 28531428 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 2047) (lo := 236) (len := 132) (W := 28531428) check rows elimOK (by decide) (by decide) cover2047 (by decide)
  decide +kernel

theorem c2047_2 : P.sumLeaves 24 2096496 128 = 54311776 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 2047) (lo := 368) (len := 128) (W := 54311776) check rows elimOK (by decide) (by decide) cover2047 (by decide)
  decide +kernel

theorem c2047_3 : P.sumLeaves 24 2096624 211 = 66638889 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 2047) (lo := 496) (len := 211) (W := 66638889) check rows elimOK (by decide) (by decide) cover2047 (by decide)
  decide +kernel

theorem c2047_4 : P.sumLeaves 24 2096835 157 = 74611633 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 2047) (lo := 707) (len := 157) (W := 74611633) check rows elimOK (by decide) (by decide) cover2047 (by decide)
  decide +kernel

theorem c2047_5 : P.sumLeaves 24 2096992 128 = 113811908 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 2047) (lo := 864) (len := 128) (W := 113811908) check rows elimOK (by decide) (by decide) cover2047 (by decide)
  decide +kernel

theorem c2047_6 : P.sumLeaves 24 2097120 32 = 59843576 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 2047) (lo := 992) (len := 32) (W := 59843576) check rows elimOK (by decide) (by decide) cover2047 (by decide)
  decide +kernel

theorem h2047 : P.leaf 34 2047 = 416256042 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(236, 18506832), (132, 28531428), (128, 54311776), (211, 66638889), (157, 74611633), (128, 113811908), (32, 59843576)]) (.cons c2047_0 (.cons c2047_1 (.cons c2047_2 (.cons c2047_3 (.cons c2047_4 (.cons c2047_5 (.cons c2047_6 (.nil)))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(2013, 48), (2014, 48), (2015, 48), (2028, 24), (2029, 24), (2030, 48), (2031, 48), (2046, 24), (2047, 24)]

theorem segOK : checkSeg 16 perms 2013 3180 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 2013 3180 336 19490108256 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 19490108256)
    (SegSum.cons (w := 48) h2013 (SegSum.cons (w := 48) h2014 (SegSum.cons (w := 48) h2015 (SegSum.cons (w := 24) h2028 (SegSum.cons (w := 24) h2029 (SegSum.cons (w := 48) h2030 (SegSum.cons (w := 48) h2031 (SegSum.cons (w := 24) h2046 (SegSum.cons (w := 24) h2047 (show SegSum (P.leaf 34) [] 0 from rfl)))))))))) (by decide)

end RACert.S4N1.C0.S17
