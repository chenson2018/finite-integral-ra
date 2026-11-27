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

namespace RACert.S4N1.C0.S60

open RACert RACert.Problem

theorem cover8167 : P.CoversSplit 24 10 8167 0xfffffffffefeaaaa0000000000000000fffffffffefeaaaa00000000000000000000000000000000000000000000000000000000000000000000000000000000fffffffffefeaaaa0000000000000000fffffffffafaaaaa00000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 524, 566, 1209, 1210, 1217, 1258, 1259, 1264]) (by decide +kernel)

theorem c8167_0 : P.sumLeaves 24 8363008 502 = 27309870 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8167) (lo := 0) (len := 502) (W := 27309870) check rows elimOK (by decide) (by decide) cover8167 (by decide)
  decide +kernel

theorem c8167_1 : P.sumLeaves 24 8363510 500 = 86068813 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8167) (lo := 502) (len := 500) (W := 86068813) check rows elimOK (by decide) (by decide) cover8167 (by decide)
  decide +kernel

theorem c8167_2 : P.sumLeaves 24 8364010 22 = 48291376 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8167) (lo := 1002) (len := 22) (W := 48291376) check rows elimOK (by decide) (by decide) cover8167 (by decide)
  decide +kernel

theorem h8167 : P.leaf 34 8167 = 161670059 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(502, 27309870), (500, 86068813), (22, 48291376)]) (.cons c8167_0 (.cons c8167_1 (.cons c8167_2 (.nil)))) (by decide) (by decide))

theorem cover8168 : P.CoversSplit 24 10 8168 0x8888000088888888000000000000000088880000888888880000000000000000000000000000000000000000000000000000000000000000000000000000000088000000880088000000000000000000880000008800880000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 523, 565, 916, 1210, 1259]) (by decide +kernel)

theorem c8168_0 : P.sumLeaves 24 8364032 1024 = 2979408 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8168) (lo := 0) (len := 1024) (W := 2979408) check rows elimOK (by decide) (by decide) cover8168 (by decide)
  decide +kernel

theorem h8168 : P.leaf 34 8168 = 2979408 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2979408)]) (.cons c8168_0 (.nil)) (by decide) (by decide))

theorem cover8169 : P.CoversSplit 24 10 8169 0xcccccccccccc88880000000000000000cccccccccccc888800000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00cc0088000000000000000000cc00cc00c800880000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 523, 916, 1209, 1210, 1217, 1259]) (by decide +kernel)

theorem c8169_0 : P.sumLeaves 24 8365056 1024 = 23120980 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8169) (lo := 0) (len := 1024) (W := 23120980) check rows elimOK (by decide) (by decide) cover8169 (by decide)
  decide +kernel

theorem h8169 : P.leaf 34 8169 = 23120980 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 23120980)]) (.cons c8169_0 (.nil)) (by decide) (by decide))

theorem cover8170 : P.CoversSplit 24 10 8170 0xaaaa0000abab0a0a0000000000000000aaaa0000abab0a0a00000000000000000000000000000000000000000000000000000000000000000000000000000000aaaa0000abab0a0a0000000000000000aaaa0000aaaa0a0a00000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 522, 523, 565, 916, 1217, 1258, 1259, 1264]) (by decide +kernel)

theorem c8170_0 : P.sumLeaves 24 8366080 1024 = 23802297 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8170) (lo := 0) (len := 1024) (W := 23802297) check rows elimOK (by decide) (by decide) cover8170 (by decide)
  decide +kernel

theorem h8170 : P.leaf 34 8170 = 23802297 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 23802297)]) (.cons c8170_0 (.nil)) (by decide) (by decide))

theorem cover8171 : P.CoversSplit 24 10 8171 0xfffffffffefeaaaa0000000000000000fffffffffefeaaaa00000000000000000000000000000000000000000000000000000000000000000000000000000000fffffffffefeaaaa0000000000000000fffffffffafaaaaa00000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 523, 916, 1209, 1210, 1217, 1258, 1259, 1264]) (by decide +kernel)

theorem c8171_0 : P.sumLeaves 24 8367104 502 = 16256260 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8171) (lo := 0) (len := 502) (W := 16256260) check rows elimOK (by decide) (by decide) cover8171 (by decide)
  decide +kernel

theorem c8171_1 : P.sumLeaves 24 8367606 500 = 48949079 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8171) (lo := 502) (len := 500) (W := 48949079) check rows elimOK (by decide) (by decide) cover8171 (by decide)
  decide +kernel

theorem c8171_2 : P.sumLeaves 24 8368106 22 = 32153264 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8171) (lo := 1002) (len := 22) (W := 32153264) check rows elimOK (by decide) (by decide) cover8171 (by decide)
  decide +kernel

theorem h8171 : P.leaf 34 8171 = 97358603 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(502, 16256260), (500, 48949079), (22, 32153264)]) (.cons c8171_0 (.cons c8171_1 (.cons c8171_2 (.nil)))) (by decide) (by decide))

theorem cover8172 : P.CoversSplit 24 10 8172 0x8888000088888888000000000000000088880000888888880000000000000000000000000000000000000000000000000000000000000000000000000000000088000000880088000000000000000000880000008800880000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 916, 1210, 1259]) (by decide +kernel)

theorem c8172_0 : P.sumLeaves 24 8368128 1024 = 11556010 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8172) (lo := 0) (len := 1024) (W := 11556010) check rows elimOK (by decide) (by decide) cover8172 (by decide)
  decide +kernel

theorem h8172 : P.leaf 34 8172 = 11556010 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 11556010)]) (.cons c8172_0 (.nil)) (by decide) (by decide))

theorem cover8173 : P.CoversSplit 24 10 8173 0xcccccccccccc88880000000000000000cccccccccccc888800000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00cc0088000000000000000000cc00cc00c800880000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 916, 1209, 1210, 1217, 1259]) (by decide +kernel)

theorem c8173_0 : P.sumLeaves 24 8369152 1024 = 53952794 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8173) (lo := 0) (len := 1024) (W := 53952794) check rows elimOK (by decide) (by decide) cover8173 (by decide)
  decide +kernel

theorem h8173 : P.leaf 34 8173 = 53952794 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 53952794)]) (.cons c8173_0 (.nil)) (by decide) (by decide))

theorem cover8174 : P.CoversSplit 24 10 8174 0xaaaa0000abab0a0a0000000000000000aaaa0000abab0a0a00000000000000000000000000000000000000000000000000000000000000000000000000000000aaaa0000abab0a0a0000000000000000aaaa0000aaaa0a0a00000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 522, 1217, 1258, 1259, 1264]) (by decide +kernel)

theorem c8174_0 : P.sumLeaves 24 8370176 1024 = 81205089 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8174) (lo := 0) (len := 1024) (W := 81205089) check rows elimOK (by decide) (by decide) cover8174 (by decide)
  decide +kernel

theorem h8174 : P.leaf 34 8174 = 81205089 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 81205089)]) (.cons c8174_0 (.nil)) (by decide) (by decide))

theorem cover8175 : P.CoversSplit 24 10 8175 0xfffffffffefeaaaa0000000000000000fffffffffefeaaaa00000000000000000000000000000000000000000000000000000000000000000000000000000000fffffffffefeaaaa0000000000000000fffffffffafaaaaa00000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 1209, 1210, 1217, 1258, 1259, 1264]) (by decide +kernel)

theorem c8175_0 : P.sumLeaves 24 8371200 502 = 40699451 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8175) (lo := 0) (len := 502) (W := 40699451) check rows elimOK (by decide) (by decide) cover8175 (by decide)
  decide +kernel

theorem c8175_1 : P.sumLeaves 24 8371702 500 = 125170908 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8175) (lo := 502) (len := 500) (W := 125170908) check rows elimOK (by decide) (by decide) cover8175 (by decide)
  decide +kernel

theorem c8175_2 : P.sumLeaves 24 8372202 22 = 62059032 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8175) (lo := 1002) (len := 22) (W := 62059032) check rows elimOK (by decide) (by decide) cover8175 (by decide)
  decide +kernel

theorem h8175 : P.leaf 34 8175 = 227929391 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(502, 40699451), (500, 125170908), (22, 62059032)]) (.cons c8175_0 (.cons c8175_1 (.cons c8175_2 (.nil)))) (by decide) (by decide))

theorem cover8179 : P.CoversSplit 24 10 8179 0xffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaccffccff88888888cc00cc0088008800ccffccff88888888cc00cc0088008800ffffffffffffaaaaffffffffffffaaaafffffffffafaaaaafffffffffafaaaaaccffccff88888888cc00cc0088008800cccccccc88888888cc00cc0088008800 :=
  coversSplit check rows (by decide) (by decide) (xs := [916, 1209, 1210, 1217, 1258, 1601, 1609]) (by decide +kernel)

theorem c8179_0 : P.sumLeaves 24 8375296 284 = 5352288 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8179) (lo := 0) (len := 284) (W := 5352288) check rows elimOK (by decide) (by decide) cover8179 (by decide)
  decide +kernel

theorem c8179_1 : P.sumLeaves 24 8375580 116 = 12658223 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8179) (lo := 284) (len := 116) (W := 12658223) check rows elimOK (by decide) (by decide) cover8179 (by decide)
  decide +kernel

theorem c8179_2 : P.sumLeaves 24 8375696 104 = 23888541 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8179) (lo := 400) (len := 104) (W := 23888541) check rows elimOK (by decide) (by decide) cover8179 (by decide)
  decide +kernel

theorem c8179_3 : P.sumLeaves 24 8375800 265 = 25215914 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8179) (lo := 504) (len := 265) (W := 25215914) check rows elimOK (by decide) (by decide) cover8179 (by decide)
  decide +kernel

theorem c8179_4 : P.sumLeaves 24 8376065 111 = 35542794 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8179) (lo := 769) (len := 111) (W := 35542794) check rows elimOK (by decide) (by decide) cover8179 (by decide)
  decide +kernel

theorem c8179_5 : P.sumLeaves 24 8376176 112 = 72938816 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8179) (lo := 880) (len := 112) (W := 72938816) check rows elimOK (by decide) (by decide) cover8179 (by decide)
  decide +kernel

theorem c8179_6 : P.sumLeaves 24 8376288 32 = 52919040 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8179) (lo := 992) (len := 32) (W := 52919040) check rows elimOK (by decide) (by decide) cover8179 (by decide)
  decide +kernel

theorem h8179 : P.leaf 34 8179 = 228515616 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(284, 5352288), (116, 12658223), (104, 23888541), (265, 25215914), (111, 35542794), (112, 72938816), (32, 52919040)]) (.cons c8179_0 (.cons c8179_1 (.cons c8179_2 (.cons c8179_3 (.cons c8179_4 (.cons c8179_5 (.cons c8179_6 (.nil)))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(8167, 48), (8168, 48), (8169, 48), (8170, 48), (8171, 48), (8172, 48), (8173, 48), (8174, 48), (8175, 48), (8179, 24)]

theorem segOK : checkSeg 16 perms 8167 8180 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 8167 8180 456 38295957072 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 38295957072)
    (SegSum.cons (w := 48) h8167 (SegSum.cons (w := 48) h8168 (SegSum.cons (w := 48) h8169 (SegSum.cons (w := 48) h8170 (SegSum.cons (w := 48) h8171 (SegSum.cons (w := 48) h8172 (SegSum.cons (w := 48) h8173 (SegSum.cons (w := 48) h8174 (SegSum.cons (w := 48) h8175 (SegSum.cons (w := 24) h8179 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))) (by decide)

end RACert.S4N1.C0.S60
