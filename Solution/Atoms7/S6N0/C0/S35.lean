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

namespace RACert.S6N0.C0.S35

open RACert RACert.Problem

theorem cover16375 : P.CoversSplit 26 10 16375 0xff00ff00ff00fa00ff00fa00ff00fa0000000000000000000000000000000000ff00f000ff00f000aa00a000aa00a0000000000000000000000000000000000000000000000000000000000000000000000000003300320000000000220022000000000000000000000000000000000000000000330030000000000022002000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 930, 972, 979, 1265, 1315, 1658]) (by decide +kernel)

theorem c16375_0 : P.sumLeaves 26 16768000 990 = 202728132 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16375) (lo := 0) (len := 990) (W := 202728132) check rows elimOK (by decide) (by decide) cover16375 (by decide)
  decide +kernel

theorem c16375_1 : P.sumLeaves 26 16768990 34 = 75925868 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16375) (lo := 990) (len := 34) (W := 75925868) check rows elimOK (by decide) (by decide) cover16375 (by decide)
  decide +kernel

theorem h16375 : P.leaf 36 16375 = 278654000 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(990, 202728132), (34, 75925868)]) (.cons c16375_0 (.cons c16375_1 (.nil))) (by decide) (by decide))

theorem cover16376 : P.CoversSplit 26 10 16376 0xf0f0f0f5f0f0f0c0f0f0f0f0f0f0f0c0f0f0f0f5f0c0f0c0a080a080a080a0800000000000000000000000000000000000000000000000000000000000000000f0f0f0f5f0c0f0c0f0f0f0f0f0c0f0c0f0c0f0c4f000f000a080a080a000a0000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 874, 923, 930, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c16376_0 : P.sumLeaves 26 16769024 813 = 6040614 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16376) (lo := 0) (len := 813) (W := 6040614) check rows elimOK (by decide) (by decide) cover16376 (by decide)
  decide +kernel

theorem c16376_1 : P.sumLeaves 26 16769837 210 = 12526510 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16376) (lo := 813) (len := 210) (W := 12526510) check rows elimOK (by decide) (by decide) cover16376 (by decide)
  decide +kernel

theorem c16376_2 : P.sumLeaves 26 16770047 1 = 578592 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16376) (lo := 1023) (len := 1) (W := 578592) check rows elimOK (by decide) (by decide) cover16376 (by decide)
  decide +kernel

theorem h16376 : P.leaf 36 16376 = 19145716 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(813, 6040614), (210, 12526510), (1, 578592)]) (.cons c16376_0 (.cons c16376_1 (.cons c16376_2 (.nil)))) (by decide) (by decide))

theorem cover16377 : P.CoversSplit 26 10 16377 0xf0f0f0f5f0f0f0c0f0f0f0f0f0f0f0c0f0f0f0f5f0c0f0c0a080a080a080a0800000000000000000000000000000000000000000000000000000000000000000f0f0f0f5f0c0f0c0f0f0f0f0f0c0f0c0f0c0f0c4f000f000a080a080a000a0000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 923, 930, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c16377_0 : P.sumLeaves 26 16770048 813 = 32388462 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16377) (lo := 0) (len := 813) (W := 32388462) check rows elimOK (by decide) (by decide) cover16377 (by decide)
  decide +kernel

theorem c16377_1 : P.sumLeaves 26 16770861 210 = 75224889 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16377) (lo := 813) (len := 210) (W := 75224889) check rows elimOK (by decide) (by decide) cover16377 (by decide)
  decide +kernel

theorem c16377_2 : P.sumLeaves 26 16771071 1 = 2332464 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16377) (lo := 1023) (len := 1) (W := 2332464) check rows elimOK (by decide) (by decide) cover16377 (by decide)
  decide +kernel

theorem h16377 : P.leaf 36 16377 = 109945815 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(813, 32388462), (210, 75224889), (1, 2332464)]) (.cons c16377_0 (.cons c16377_1 (.cons c16377_2 (.nil)))) (by decide) (by decide))

theorem cover16378 : P.CoversSplit 26 10 16378 0xf0f0f0f5f0f0f0c0f0f0f0f0f0f0f0c0f0f0f0f5f0c0f0c0a080a080a080a0800000505000005040000000000000000000005050000050400000000000000000f0f0f0f5f0c0f0c0f0f0f0f0f0c0f0c0f0c0f0c4f000f000a080a080a000a0000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 874, 930, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c16378_0 : P.sumLeaves 26 16771072 710 = 46093383 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16378) (lo := 0) (len := 710) (W := 46093383) check rows elimOK (by decide) (by decide) cover16378 (by decide)
  decide +kernel

theorem c16378_1 : P.sumLeaves 26 16771782 287 = 88697764 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16378) (lo := 710) (len := 287) (W := 88697764) check rows elimOK (by decide) (by decide) cover16378 (by decide)
  decide +kernel

theorem c16378_2 : P.sumLeaves 26 16772069 27 = 31351664 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16378) (lo := 997) (len := 27) (W := 31351664) check rows elimOK (by decide) (by decide) cover16378 (by decide)
  decide +kernel

theorem h16378 : P.leaf 36 16378 = 166142811 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(710, 46093383), (287, 88697764), (27, 31351664)]) (.cons c16378_0 (.cons c16378_1 (.cons c16378_2 (.nil)))) (by decide) (by decide))

theorem cover16379 : P.CoversSplit 26 10 16379 0xf0f0f0f5f0f0f0c0f0f0f0f0f0f0f0c0f0f0f0f5f0c0f0c0a080a080a080a0800000505000005040000000000000000000005050000050400000000000000000f0f0f0f5f0c0f0c0f0f0f0f0f0c0f0c0f0c0f0c4f000f000a080a080a000a0000000505000005040000000000000000000005040000050000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 930, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c16379_0 : P.sumLeaves 26 16772096 503 = 75242402 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16379) (lo := 0) (len := 503) (W := 75242402) check rows elimOK (by decide) (by decide) cover16379 (by decide)
  decide +kernel

theorem c16379_1 : P.sumLeaves 26 16772599 472 = 177086882 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16379) (lo := 503) (len := 472) (W := 177086882) check rows elimOK (by decide) (by decide) cover16379 (by decide)
  decide +kernel

theorem c16379_2 : P.sumLeaves 26 16773071 49 = 89719558 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16379) (lo := 975) (len := 49) (W := 89719558) check rows elimOK (by decide) (by decide) cover16379 (by decide)
  decide +kernel

theorem h16379 : P.leaf 36 16379 = 342048842 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(503, 75242402), (472, 177086882), (49, 89719558)]) (.cons c16379_0 (.cons c16379_1 (.cons c16379_2 (.nil)))) (by decide) (by decide))

theorem cover16382 : P.CoversSplit 26 10 16382 0xfffffffafffffac8fffffafafffffac8fffffffaffccfac8aa88aa88aa88aa88fffffafafffffac8aaaaaaaaaaaaaa88fffffafaffccfac8aa88aa88aa88aa88fffffffaffccfac8fffffafaffccfac8ffccffc8ffccfac8aa88aa88aa88aa880000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [874, 930, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c16382_0 : P.sumLeaves 26 16775168 427 = 99696118 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16382) (lo := 0) (len := 427) (W := 99696118) check rows elimOK (by decide) (by decide) cover16382 (by decide)
  decide +kernel

theorem c16382_1 : P.sumLeaves 26 16775595 152 = 190635422 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16382) (lo := 427) (len := 152) (W := 190635422) check rows elimOK (by decide) (by decide) cover16382 (by decide)
  decide +kernel

theorem c16382_2 : P.sumLeaves 26 16775747 149 = 146204416 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16382) (lo := 579) (len := 149) (W := 146204416) check rows elimOK (by decide) (by decide) cover16382 (by decide)
  decide +kernel

theorem c16382_3 : P.sumLeaves 26 16775896 153 = 195508718 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16382) (lo := 728) (len := 153) (W := 195508718) check rows elimOK (by decide) (by decide) cover16382 (by decide)
  decide +kernel

theorem c16382_4 : P.sumLeaves 26 16776049 116 = 297885314 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16382) (lo := 881) (len := 116) (W := 297885314) check rows elimOK (by decide) (by decide) cover16382 (by decide)
  decide +kernel

theorem c16382_5 : P.sumLeaves 26 16776165 27 = 151276762 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16382) (lo := 997) (len := 27) (W := 151276762) check rows elimOK (by decide) (by decide) cover16382 (by decide)
  decide +kernel

theorem h16382 : P.leaf 36 16382 = 1081206750 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(427, 99696118), (152, 190635422), (149, 146204416), (153, 195508718), (116, 297885314), (27, 151276762)]) (.cons c16382_0 (.cons c16382_1 (.cons c16382_2 (.cons c16382_3 (.cons c16382_4 (.cons c16382_5 (.nil))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(16375, 360), (16376, 360), (16377, 360), (16378, 720), (16379, 720), (16382, 360)]

theorem segOK : checkSeg 20 perms 16375 16383 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 16375 16383 2880 901920811320 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 901920811320)
    (SegSum.cons (w := 360) h16375 (SegSum.cons (w := 360) h16376 (SegSum.cons (w := 360) h16377 (SegSum.cons (w := 720) h16378 (SegSum.cons (w := 720) h16379 (SegSum.cons (w := 360) h16382 (show SegSum (P.leaf 36) [] 0 from rfl))))))) (by decide)

end RACert.S6N0.C0.S35
