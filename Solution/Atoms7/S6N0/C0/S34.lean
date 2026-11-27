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

namespace RACert.S6N0.C0.S34

open RACert RACert.Problem

theorem cover16371 : P.CoversSplit 26 10 16371 0xf000f000f000f000f000f000f000f0000000000000000000000000000000000000000a0000000a0000000a0000000a000000000000000000000000000000000000000000000000000000000000000000000000003000300000000000200020000000000000000000000000000000000000000000000002000000000000000200 :=
  coversProjected check rows (by decide) (by decide) (xs := [481, 489, 930, 972, 979, 1315, 1658]) (ps := [(13, [923], [972])]) (by decide +kernel)

theorem c16371_0 : P.sumLeaves 26 16763904 1024 = 33682912 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16371) (lo := 0) (len := 1024) (W := 33682912) check rows elimOK (by decide) (by decide) cover16371 (by decide)
  decide +kernel

theorem h16371 : P.leaf 36 16371 = 33682912 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 33682912)]) (.cons c16371_0 (.nil)) (by decide) (by decide))

theorem cover16374 : P.CoversSplit 26 10 16374 0xff00ff00ff00fa00ff00fa00ff00fa0000000000000000000000000000000000ff00f000ff00f000aa00a000aa00a0000000000000000000000000000000000000000000000000000000000000000000000000003300320000000000220022000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 880, 930, 972, 979, 1265, 1315, 1658]) (by decide +kernel)

theorem c16374_0 : P.sumLeaves 26 16766976 1007 = 74077076 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16374) (lo := 0) (len := 1007) (W := 74077076) check rows elimOK (by decide) (by decide) cover16374 (by decide)
  decide +kernel

theorem c16374_1 : P.sumLeaves 26 16767983 17 = 21184184 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16374) (lo := 1007) (len := 17) (W := 21184184) check rows elimOK (by decide) (by decide) cover16374 (by decide)
  decide +kernel

theorem h16374 : P.leaf 36 16374 = 95261260 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1007, 74077076), (17, 21184184)]) (.cons c16374_0 (.cons c16374_1 (.nil))) (by decide) (by decide))

theorem cover16375 : P.CoversSplit 26 10 16375 0xff00ff00ff00fa00ff00fa00ff00fa0000000000000000000000000000000000ff00f000ff00f000aa00a000aa00a0000000000000000000000000000000000000000000000000000000000000000000000000003300320000000000220022000000000000000000000000000000000000000000330030000000000022002000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 930, 972, 979, 1265, 1315, 1658]) (by decide +kernel)

theorem c16375_0 : P.sumLeaves 26 16768000 64 = 28224 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16375) (lo := 0) (len := 64) (W := 28224) check rows elimOK (by decide) (by decide) cover16375 (by decide)
  decide +kernel

theorem contract16375_1 : P.leaf 32 262001 = 39936 := by
  exact leaf_contract_factors (k := 32) (b := 17) (H := 262001) (ss := [(22, 1, 433), (2, 1, 482), (3, 1, 537), (4, 1, 580), (5, 1, 629), (7, 1, 825), (13, 1, 923), (29, 0, 930), (33, 0, 930), (31, 1, 489), (6, 1, 636), (11, 0, 930), (12, 0, 979), (8, 1, 1217), (9, 1, 1609)]) (ids := [8, 25, 12, 13, 14, 16, 17, 19, 22, 24, 26, 28, 30, 15, 18, 21, 23]) (cs := [1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 0, 1, 4, 5, 6, 15, 7, 8, 16, 9, 1, 17, 10, 18, 11, 3, 12, 0, 13, 1, 14, 0]) (bs := [2, 11, 4]) (W := 39936) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c16375_1 : P.sumLeaves 26 16768064 64 = 39936 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 262001) rows (by decide) (by decide)).symm.trans contract16375_1

theorem c16375_2 : P.sumLeaves 26 16768128 879 = 234710772 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16375) (lo := 128) (len := 879) (W := 234710772) check rows elimOK (by decide) (by decide) cover16375 (by decide)
  decide +kernel

theorem c16375_3 : P.sumLeaves 26 16769007 17 = 43875068 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16375) (lo := 1007) (len := 17) (W := 43875068) check rows elimOK (by decide) (by decide) cover16375 (by decide)
  decide +kernel

theorem h16375 : P.leaf 36 16375 = 278654000 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 28224), (64, 39936), (879, 234710772), (17, 43875068)]) (.cons c16375_0 (.cons c16375_1 (.cons c16375_2 (.cons c16375_3 (.nil))))) (by decide) (by decide))

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

theorem c16379_0 : P.sumLeaves 26 16772096 192 = 61880 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16379) (lo := 0) (len := 192) (W := 61880) check rows elimOK (by decide) (by decide) cover16379 (by decide)
  decide +kernel

theorem contract16379_1 : P.leaf 32 262067 = 93104 := by
  exact leaf_contract_factors (k := 32) (b := 18) (H := 262067) (ss := [(22, 1, 433), (2, 1, 482), (3, 1, 531), (4, 1, 580), (5, 1, 629), (6, 1, 636), (7, 1, 825), (21, 1, 929), (28, 0, 972), (32, 0, 972), (8, 1, 1217), (30, 1, 1315), (13, 0, 972), (9, 1, 1609)]) (ids := [9, 10, 12, 13, 14, 15, 16, 17, 18, 22, 23, 24, 27, 29, 31, 8, 21, 25]) (cs := [1, 1, 1, 1, 1, 1, 1, 1, 17, 2, 3, 0, 4, 5, 6, 7, 8, 9, 10, 1, 1, 18, 11, 12, 13, 19, 0, 14, 1, 15, 0, 16]) (bs := [15, 3]) (W := 93104) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c16379_1 : P.sumLeaves 26 16772288 64 = 93104 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 262067) rows (by decide) (by decide)).symm.trans contract16379_1

theorem c16379_2 : P.sumLeaves 26 16772352 454 = 86968168 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16379) (lo := 256) (len := 454) (W := 86968168) check rows elimOK (by decide) (by decide) cover16379 (by decide)
  decide +kernel

theorem c16379_3 : P.sumLeaves 26 16772806 287 = 198550634 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16379) (lo := 710) (len := 287) (W := 198550634) check rows elimOK (by decide) (by decide) cover16379 (by decide)
  decide +kernel

theorem c16379_4 : P.sumLeaves 26 16773093 27 = 56375056 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16379) (lo := 997) (len := 27) (W := 56375056) check rows elimOK (by decide) (by decide) cover16379 (by decide)
  decide +kernel

theorem h16379 : P.leaf 36 16379 = 342048842 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(192, 61880), (64, 93104), (454, 86968168), (287, 198550634), (27, 56375056)]) (.cons c16379_0 (.cons c16379_1 (.cons c16379_2 (.cons c16379_3 (.cons c16379_4 (.nil)))))) (by decide) (by decide))

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

def seg : List (ℕ × ℕ) := [(16371, 720), (16374, 360), (16375, 360), (16376, 360), (16377, 360), (16378, 720), (16379, 720), (16382, 360)]

theorem segOK : checkSeg 20 perms 16371 16383 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 16371 16383 3960 960466561560 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 960466561560)
    (SegSum.cons (w := 720) h16371 (SegSum.cons (w := 360) h16374 (SegSum.cons (w := 360) h16375 (SegSum.cons (w := 360) h16376 (SegSum.cons (w := 360) h16377 (SegSum.cons (w := 720) h16378 (SegSum.cons (w := 720) h16379 (SegSum.cons (w := 360) h16382 (show SegSum (P.leaf 36) [] 0 from rfl))))))))) (by decide)

end RACert.S6N0.C0.S34
