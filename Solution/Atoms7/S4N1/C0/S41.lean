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

namespace RACert.S4N1.C0.S41

open RACert RACert.Problem

theorem cover7039 : P.CoversSplit 24 10 7039 0xffffffffafafa0a0ffffffffafafa0a0ffffffffafafa0a0ffffffffafafa0a0cc33cc3380008000cc00cc0080008000cc33cc3380008000cc00cc0080008000ffffffffafafa0a0ffffffffafafa0a0000000000000000000000000000000000000000000000000cc00cc008000800000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [572, 859, 1202, 1209, 1217, 1258, 1259, 1308, 1601, 1609]) (by decide +kernel)

theorem c7039_0 : P.sumLeaves 24 7207936 502 = 8550516 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7039) (lo := 0) (len := 502) (W := 8550516) check rows elimOK (by decide) (by decide) cover7039 (by decide)
  decide +kernel

theorem c7039_1 : P.sumLeaves 24 7208438 312 = 23413694 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7039) (lo := 502) (len := 312) (W := 23413694) check rows elimOK (by decide) (by decide) cover7039 (by decide)
  decide +kernel

theorem c7039_2 : P.sumLeaves 24 7208750 128 = 40619048 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7039) (lo := 814) (len := 128) (W := 40619048) check rows elimOK (by decide) (by decide) cover7039 (by decide)
  decide +kernel

theorem c7039_3 : P.sumLeaves 24 7208878 82 = 89706577 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7039) (lo := 942) (len := 82) (W := 89706577) check rows elimOK (by decide) (by decide) cover7039 (by decide)
  decide +kernel

theorem h7039 : P.leaf 34 7039 = 162289835 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(502, 8550516), (312, 23413694), (128, 40619048), (82, 89706577)]) (.cons c7039_0 (.cons c7039_1 (.cons c7039_2 (.cons c7039_3 (.nil))))) (by decide) (by decide))

theorem cover11490 : P.CoversSplit 24 10 11490 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 522, 524, 566, 858, 865, 1209, 1217, 1258, 1266, 1609]) (by decide +kernel)

theorem h11490 : P.leaf 34 11490 = 43212 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 11490) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 11490) (weight := fun _ => 1) (xs := [511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover11490 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h7136 : P.leaf 34 7136 = 43212 :=
  orient32 (v := 11490) (by decide) (by decide +kernel) h11490

theorem cover18317 : P.CoversSplit 24 10 18317 0x8800880000000000880088000000000088008800000000008800000000000000000000000000000000000000000000000000000000000000000000000000000088008800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 517, 522, 528, 916, 921, 1251, 1259]) (ps := [(14, [923], [1266])]) (by decide +kernel)

theorem h18317 : P.leaf 34 18317 = 1131966 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 18317) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 18317) (weight := fun _ => 1) (xs := [491, 495, 507, 511, 827, 831, 875, 879, 891, 895, 939, 943, 955, 959, 1003, 1007, 1019, 1023]) check rows elimOK (by decide) (by decide) cover18317 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h7137 : P.leaf 34 7137 = 1131966 :=
  orient4 (v := 18317) (by decide) (by decide +kernel) h18317

theorem cover7139 : P.CoversSplit 24 10 7139 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 523, 859, 916, 1202, 1209, 1210, 1251, 1259, 1264]) (by decide +kernel)

noncomputable def f7139 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (7310336 + i)

theorem c7139_0 : rowSum f7139 0 1024 = 16003415 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 7139) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover7139 (by decide)
  decide +kernel

theorem sum7139 : rowSum f7139 0 1024 = 16003415 :=
  c7139_0

theorem h7139 : P.leaf 34 7139 = 16003415 :=
  leaf_weighted (k := 24) (d := 10) (H := 7139) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 7139) (by decide) (by decide +kernel)) sum7139

theorem cover7140 : P.CoversSplit 24 10 7140 0x8888000000000000000000000000000080800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 524, 566, 859, 879, 916, 1202, 1210, 1259, 1264]) (by decide +kernel)

theorem h7140 : P.leaf 34 7140 = 648280 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7140) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7140) (weight := fun _ => 1) (xs := [383, 507, 511, 887, 895, 1011, 1015, 1019, 1023]) check rows elimOK (by decide) (by decide) cover7140 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7141 : P.CoversSplit 24 10 7141 0xcccc0000000000000000000000000000cccc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 524, 566, 859, 879, 916, 1202, 1209, 1210, 1251, 1259]) (by decide +kernel)

theorem h7141 : P.leaf 34 7141 = 6840542 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7141) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7141) (weight := fun _ => 1) (xs := [378, 379, 382, 383, 506, 507, 510, 511, 882, 883, 886, 887, 890, 891, 894, 895, 1010, 1011, 1014, 1015, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover7141 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7142 : P.CoversSplit 24 10 7142 0xaaaa0000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000aaaa0000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 522, 524, 566, 859, 879, 1210, 1259, 1264]) (by decide +kernel)

theorem h7142 : P.leaf 34 7142 = 7891498 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7142) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7142) (weight := fun _ => 1) (xs := [373, 375, 381, 383, 497, 499, 501, 503, 505, 507, 509, 511, 885, 887, 893, 895, 1009, 1011, 1013, 1015, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover7142 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7143 : P.CoversSplit 24 10 7143 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 524, 566, 859, 1202, 1209, 1210, 1251, 1259, 1264]) (by decide +kernel)

theorem c7143_0 : P.sumLeaves 24 7314432 1024 = 34305216 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7143) (lo := 0) (len := 1024) (W := 34305216) check rows elimOK (by decide) (by decide) cover7143 (by decide)
  decide +kernel

theorem h7143 : P.leaf 34 7143 = 34305216 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 34305216)]) (.cons c7143_0 (.nil)) (by decide) (by decide))

theorem cover7148 : P.CoversSplit 24 10 7148 0x8888000000000000000000000000000080800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 859, 879, 916, 1202, 1210, 1259, 1264]) (by decide +kernel)

theorem h7148 : P.leaf 34 7148 = 3685160 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 7148) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 7148) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7148) (weight := rowWeight keep1 twice1) (xs := [383, 507, 511, 887, 895, 1011, 1015, 1019, 1023]) check rows elimOK (by decide) (by decide) cover7148 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7149 : P.CoversSplit 24 10 7149 0xcccc0000000000000000000000000000cccc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 879, 916, 1202, 1209, 1210, 1251, 1259]) (by decide +kernel)

theorem h7149 : P.leaf 34 7149 = 22498770 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7149) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7149) (weight := fun _ => 1) (xs := [378, 379, 382, 383, 506, 507, 510, 511, 882, 883, 886, 887, 890, 891, 894, 895, 1010, 1011, 1014, 1015, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover7149 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7151 : P.CoversSplit 24 10 7151 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 1202, 1209, 1210, 1251, 1259, 1264]) (by decide +kernel)

noncomputable def f7151 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (7322624 + i)

theorem c7151_0 : rowSum f7151 0 1024 = 88616980 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 7151) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover7151 (by decide)
  decide +kernel

theorem sum7151 : rowSum f7151 0 1024 = 88616980 :=
  c7151_0

theorem h7151 : P.leaf 34 7151 = 88616980 :=
  leaf_weighted (k := 24) (d := 10) (H := 7151) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 7151) (by decide) (by decide +kernel)) sum7151

theorem cover11491 : P.CoversSplit 24 10 11491 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 524, 573, 858, 865, 1209, 1217, 1258, 1266, 1609]) (by decide +kernel)

theorem h11491 : P.leaf 34 11491 = 690130 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 11491) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 11491) (weight := fun _ => 1) (xs := [511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover11491 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h7152 : P.leaf 34 7152 = 690130 :=
  orient32 (v := 11491) (by decide) (by decide +kernel) h11491

theorem cover18319 : P.CoversSplit 24 10 18319 0xaaaaaaaa00000000aa88aa8800000000aaaaaaaa00000000aa880000000000008888888800000000aa00aa00000000008888888800000000aa00000000000000aaaaaaaa000000000000000000000000aaaaaaaa0000000000880000000000000000000000000000008800000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 517, 522, 528, 916, 1251, 1259, 1308, 1601]) (ps := [(18, [1308], [1264])]) (by decide +kernel)

theorem c18319_0 : P.sumLeaves 24 18758656 320 = 51184 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 18319) (lo := 0) (len := 320) (W := 51184) check rows elimOK (by decide) (by decide) cover18319 (by decide)
  decide +kernel

theorem contract18319_1 : P.leaf 30 293109 = 0 := by
  exact leaf_contract_zero (ss := [(3, 1, 524), (26, 1, 528), (31, 1, 528), (14, 0, 1266), (8, 1, 531), (12, 1, 867)]) (q := 874) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c18319_1 : P.sumLeaves 24 18758976 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 293109) rows (by decide) (by decide)).symm.trans contract18319_1

theorem c18319_2 : P.sumLeaves 24 18759040 640 = 16102899 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 18319) (lo := 384) (len := 640) (W := 16102899) check rows elimOK (by decide) (by decide) cover18319 (by decide)
  decide +kernel

theorem h18319 : P.leaf 34 18319 = 16154083 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(320, 51184), (64, 0), (640, 16102899)]) (.cons c18319_0 (.cons c18319_1 (.cons c18319_2 (.nil)))) (by decide) (by decide))

theorem h7153 : P.leaf 34 7153 = 16154083 :=
  orient4 (v := 18319) (by decide) (by decide +kernel) h18319

theorem cover7155 : P.CoversSplit 24 10 7155 0xffffffffafafa0a0ffffffffafafa0a0ffffffffafafa0a0ffffffffafafa0a0ccffccff88888080cc00cc0088008000ccffccff88888080cc00cc0088008000ffffffffafafa0a0ffffffffafafa0a0ffffffffaaaaa0a0ffffffffaaaaa0a0ccffccff88888080cc00cc0088008000cccccccc88888080cc00cc0088008000 :=
  coversSplit check rows (by decide) (by decide) (xs := [859, 916, 1202, 1209, 1217, 1258, 1259, 1601, 1609]) (by decide +kernel)

noncomputable def f7155 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (7326720 + i)

theorem c7155_0 : rowSum f7155 0 319 = 7123528 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 7155) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover7155 (by decide)
  decide +kernel

theorem c7155_1 : rowSum f7155 319 182 = 22043428 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 7155) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover7155 (by decide)
  decide +kernel

theorem c7155_2 : rowSum f7155 501 523 = 55097507 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 7155) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover7155 (by decide)
  decide +kernel

theorem sum7155 : rowSum f7155 0 1024 = 84264463 :=
  rowSum_append (F := f7155) (lo := 0) (n := 319) (m := 705) (A := 7123528) (B := 77140935) c7155_0 (rowSum_append (F := f7155) (lo := 319) (n := 182) (m := 523) (A := 22043428) (B := 55097507) c7155_1 (c7155_2))

theorem h7155 : P.leaf 34 7155 = 84264463 :=
  leaf_weighted (k := 24) (d := 10) (H := 7155) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 7155) (by decide) (by decide +kernel)) sum7155

theorem cover18350 : P.CoversSplit 24 10 18350 0xaaaa0000aa000000aaaa0000aa000000aaaa000000000000aaaa0000000000008888000088000000888800008800000088880000000000008888000000000000aaaa0000aa0000000000000000000000aaaa00000000000000220000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 517, 522, 860, 872, 916, 1202, 1259, 1601]) (by decide +kernel)

theorem c18350_0 : P.sumLeaves 24 18790400 1024 = 9495862 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 18350) (lo := 0) (len := 1024) (W := 9495862) check rows elimOK (by decide) (by decide) cover18350 (by decide)
  decide +kernel

theorem h18350 : P.leaf 34 18350 = 9495862 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 9495862)]) (.cons c18350_0 (.nil)) (by decide) (by decide))

theorem h7156 : P.leaf 34 7156 = 9495862 :=
  orient4 (v := 18350) (by decide) (by decide +kernel) h18350

theorem cover18351 : P.CoversSplit 24 10 18351 0xfffffffffa000000fffffffffa000000aaaaafaf00000000aaaa000000000000cccccccc88000000ffccffccaa00000088888c8c00000000aa88000000000000fffffffffa0000000000000000000000aaaaafaf0000000000220000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 860, 872, 916, 1202, 1210, 1251, 1259, 1601]) (by decide +kernel)

theorem c18351_0 : P.sumLeaves 24 18791424 696 = 10395987 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 18351) (lo := 0) (len := 696) (W := 10395987) check rows elimOK (by decide) (by decide) cover18351 (by decide)
  decide +kernel

theorem c18351_1 : P.sumLeaves 24 18792120 294 = 23971447 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 18351) (lo := 696) (len := 294) (W := 23971447) check rows elimOK (by decide) (by decide) cover18351 (by decide)
  decide +kernel

theorem c18351_2 : P.sumLeaves 24 18792414 34 = 22718836 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 18351) (lo := 990) (len := 34) (W := 22718836) check rows elimOK (by decide) (by decide) cover18351 (by decide)
  decide +kernel

theorem h18351 : P.leaf 34 18351 = 57086270 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(696, 10395987), (294, 23971447), (34, 22718836)]) (.cons c18351_0 (.cons c18351_1 (.cons c18351_2 (.nil)))) (by decide) (by decide))

theorem h7157 : P.leaf 34 7157 = 57086270 :=
  orient4 (v := 18351) (by decide) (by decide +kernel) h18351

theorem cover35759 : P.CoversSplit 24 10 35759 0xfffffffff0f0a0a0fffffffff0f0a0a0ffffffff0000a0a0ffff000000000000cccccccc80008000ff00ff00a000a000cccccccc00008000ff00000000000000fffffffff0f0a0a00000000000000000ffffffff0000000000ff000000000000000000000080008000cc008800800080000000000000000000cc000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 859, 915, 1202, 1209, 1217, 1251, 1258, 1308, 1601]) (ps := [(19, [1209], [1264])]) (by decide +kernel)

theorem c35759_0 : P.sumLeaves 24 36617216 256 = 302054 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 35759) (lo := 0) (len := 256) (W := 302054) check rows elimOK (by decide) (by decide) cover35759 (by decide)
  decide +kernel

theorem contract35759_1 : P.leaf 30 572148 = 0 := by
  exact leaf_contract_zero (ss := [(3, 1, 529), (30, 1, 1251), (31, 1, 1251), (16, 0, 1258), (12, 1, 958), (29, 0, 1258), (19, 1, 1264), (14, 0, 1272), (8, 1, 923), (20, 1, 1266), (21, 0, 1272), (13, 0, 1314), (27, 1, 915), (7, 1, 922)]) (q := 1315) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c35759_1 : P.sumLeaves 24 36617472 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 572148) rows (by decide) (by decide)).symm.trans contract35759_1

theorem contract35759_2 : P.leaf 30 572149 = 0 := by
  exact leaf_contract_zero (ss := [(3, 1, 529), (14, 0, 1272), (12, 1, 866), (8, 1, 923), (20, 1, 1266), (21, 0, 1272), (31, 1, 1308)]) (q := 1315) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c35759_2 : P.sumLeaves 24 36617536 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 572149) rows (by decide) (by decide)).symm.trans contract35759_2

theorem c35759_3 : P.sumLeaves 24 36617600 363 = 13934350 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 35759) (lo := 384) (len := 363) (W := 13934350) check rows elimOK (by decide) (by decide) cover35759 (by decide)
  decide +kernel

theorem c35759_4 : P.sumLeaves 24 36617963 202 = 18727584 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 35759) (lo := 747) (len := 202) (W := 18727584) check rows elimOK (by decide) (by decide) cover35759 (by decide)
  decide +kernel

theorem c35759_5 : P.sumLeaves 24 36618165 75 = 31930818 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 35759) (lo := 949) (len := 75) (W := 31930818) check rows elimOK (by decide) (by decide) cover35759 (by decide)
  decide +kernel

theorem h35759 : P.leaf 34 35759 = 64894806 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 302054), (64, 0), (64, 0), (363, 13934350), (202, 18727584), (75, 31930818)]) (.cons c35759_0 (.cons c35759_1 (.cons c35759_2 (.cons c35759_3 (.cons c35759_4 (.cons c35759_5 (.nil))))))) (by decide) (by decide))

theorem h7158 : P.leaf 34 7158 = 64894806 :=
  orient24 (v := 35759) (by decide) (by decide +kernel) h35759

def seg : List (ℕ × ℕ) := [(7039, 48), (7136, 24), (7137, 48), (7139, 24), (7140, 48), (7141, 48), (7142, 48), (7143, 48), (7148, 24), (7149, 48), (7151, 24), (7152, 24), (7153, 48), (7155, 24), (7156, 48), (7157, 48), (7158, 48)]

theorem segOK : checkSeg 16 perms 7039 7159 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 7039 7159 672 23034662784 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 23034662784)
    (SegSum.cons (w := 48) h7039 (SegSum.cons (w := 24) h7136 (SegSum.cons (w := 48) h7137 (SegSum.cons (w := 24) h7139 (SegSum.cons (w := 48) h7140 (SegSum.cons (w := 48) h7141 (SegSum.cons (w := 48) h7142 (SegSum.cons (w := 48) h7143 (SegSum.cons (w := 24) h7148 (SegSum.cons (w := 48) h7149 (SegSum.cons (w := 24) h7151 (SegSum.cons (w := 24) h7152 (SegSum.cons (w := 48) h7153 (SegSum.cons (w := 24) h7155 (SegSum.cons (w := 48) h7156 (SegSum.cons (w := 48) h7157 (SegSum.cons (w := 48) h7158 (show SegSum (P.leaf 34) [] 0 from rfl)))))))))))))))))) (by decide)

end RACert.S4N1.C0.S41
