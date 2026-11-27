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

namespace RACert.S6N0.C0.S75

open RACert RACert.Problem

theorem cover98154 : P.CoversSplit 26 10 98154 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0c000000005000000000000000000000000000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f000f00000000005000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 874, 972, 979, 1266, 1315, 1322, 1658]) (by decide +kernel)

theorem c98154_0 : P.sumLeaves 26 100509696 974 = 49872664 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98154) (lo := 0) (len := 974) (W := 49872664) check rows elimOK (by decide) (by decide) cover98154 (by decide)
  decide +kernel

theorem c98154_1 : P.sumLeaves 26 100510670 50 = 69885918 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98154) (lo := 974) (len := 50) (W := 69885918) check rows elimOK (by decide) (by decide) cover98154 (by decide)
  decide +kernel

theorem h98154 : P.leaf 36 98154 = 119758582 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(974, 49872664), (50, 69885918)]) (.cons c98154_0 (.cons c98154_1 (.nil))) (by decide) (by decide))

theorem cover98155 : P.CoversSplit 26 10 98155 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0c000000005000000000000000000000000000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f000f00000000005000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 579, 972, 979, 1266, 1315, 1322, 1658]) (by decide +kernel)

theorem c98155_0 : P.sumLeaves 26 100510720 974 = 137474389 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98155) (lo := 0) (len := 974) (W := 137474389) check rows elimOK (by decide) (by decide) cover98155 (by decide)
  decide +kernel

theorem c98155_1 : P.sumLeaves 26 100511694 50 = 132490876 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98155) (lo := 974) (len := 50) (W := 132490876) check rows elimOK (by decide) (by decide) cover98155 (by decide)
  decide +kernel

theorem h98155 : P.leaf 36 98155 = 269965265 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(974, 137474389), (50, 132490876)]) (.cons c98155_0 (.cons c98155_1 (.nil))) (by decide) (by decide))

theorem cover98156 : P.CoversSplit 26 10 98156 0xfffffffffffffafa0000000000000000fffffffffffcfac805050500050000000000000000000000000000000000000000000000000000000000000000000000fffffffffffffafa0000000000000000ffffffffff00fa0005050500050000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 874, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98156_0 : P.sumLeaves 26 100511744 494 = 12505664 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98156) (lo := 0) (len := 494) (W := 12505664) check rows elimOK (by decide) (by decide) cover98156 (by decide)
  decide +kernel

theorem c98156_1 : P.sumLeaves 26 100512238 485 = 26022720 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98156) (lo := 494) (len := 485) (W := 26022720) check rows elimOK (by decide) (by decide) cover98156 (by decide)
  decide +kernel

theorem c98156_2 : P.sumLeaves 26 100512723 45 = 51423500 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98156) (lo := 979) (len := 45) (W := 51423500) check rows elimOK (by decide) (by decide) cover98156 (by decide)
  decide +kernel

theorem h98156 : P.leaf 36 98156 = 89951884 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(494, 12505664), (485, 26022720), (45, 51423500)]) (.cons c98156_0 (.cons c98156_1 (.cons c98156_2 (.nil)))) (by decide) (by decide))

theorem cover98157 : P.CoversSplit 26 10 98157 0xfffffffffffffafa0000000000000000fffffffffffcfac805050500050000000000000000000000000000000000000000000000000000000000000000000000fffffffffffffafa0000000000000000ffffffffff00fa0005050500050000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 923, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98157_0 : P.sumLeaves 26 100512768 494 = 32413089 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98157) (lo := 0) (len := 494) (W := 32413089) check rows elimOK (by decide) (by decide) cover98157 (by decide)
  decide +kernel

theorem c98157_1 : P.sumLeaves 26 100513262 485 = 59825724 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98157) (lo := 494) (len := 485) (W := 59825724) check rows elimOK (by decide) (by decide) cover98157 (by decide)
  decide +kernel

theorem c98157_2 : P.sumLeaves 26 100513747 45 = 84381290 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98157) (lo := 979) (len := 45) (W := 84381290) check rows elimOK (by decide) (by decide) cover98157 (by decide)
  decide +kernel

theorem h98157 : P.leaf 36 98157 = 176620103 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(494, 32413089), (485, 59825724), (45, 84381290)]) (.cons c98157_0 (.cons c98157_1 (.cons c98157_2 (.nil)))) (by decide) (by decide))

theorem cover98158 : P.CoversSplit 26 10 98158 0xfffffffffffffafa0000000000000000fffffffffffcfac805050500050000000000000000000000000000000000000000000000000000000000000000000000fffffffffffffafa0000000000000000ffffffffff00fa0005050500050000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 874, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98158_0 : P.sumLeaves 26 100513792 494 = 82160260 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98158) (lo := 0) (len := 494) (W := 82160260) check rows elimOK (by decide) (by decide) cover98158 (by decide)
  decide +kernel

theorem c98158_1 : P.sumLeaves 26 100514286 485 = 277470820 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98158) (lo := 494) (len := 485) (W := 277470820) check rows elimOK (by decide) (by decide) cover98158 (by decide)
  decide +kernel

theorem c98158_2 : P.sumLeaves 26 100514771 45 = 339231494 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98158) (lo := 979) (len := 45) (W := 339231494) check rows elimOK (by decide) (by decide) cover98158 (by decide)
  decide +kernel

theorem h98158 : P.leaf 36 98158 = 698862574 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(494, 82160260), (485, 277470820), (45, 339231494)]) (.cons c98158_0 (.cons c98158_1 (.cons c98158_2 (.nil)))) (by decide) (by decide))

theorem cover98159 : P.CoversSplit 26 10 98159 0xfffffffffffffafa0000000000000000fffffffffffcfac805050500050000000000000000000000000000000000000000000000000000000000000000000000fffffffffffffafa0000000000000000ffffffffff00fa0005050500050000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98159_0 : P.sumLeaves 26 100514816 494 = 190445258 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98159) (lo := 0) (len := 494) (W := 190445258) check rows elimOK (by decide) (by decide) cover98159 (by decide)
  decide +kernel

theorem c98159_1 : P.sumLeaves 26 100515310 485 = 592492169 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98159) (lo := 494) (len := 485) (W := 592492169) check rows elimOK (by decide) (by decide) cover98159 (by decide)
  decide +kernel

theorem c98159_2 : P.sumLeaves 26 100515795 45 = 478563036 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98159) (lo := 979) (len := 45) (W := 478563036) check rows elimOK (by decide) (by decide) cover98159 (by decide)
  decide +kernel

theorem h98159 : P.leaf 36 98159 = 1261500463 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(494, 190445258), (485, 592492169), (45, 478563036)]) (.cons c98159_0 (.cons c98159_1 (.cons c98159_2 (.nil)))) (by decide) (by decide))

theorem cover98163 : P.CoversSplit 26 10 98163 0xf000f000f000f0000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f000f00000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 972, 979, 1658, 1665]) (by decide +kernel)

theorem c98163_0 : P.sumLeaves 26 100518912 1024 = 86137904 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98163) (lo := 0) (len := 1024) (W := 86137904) check rows elimOK (by decide) (by decide) cover98163 (by decide)
  decide +kernel

theorem h98163 : P.leaf 36 98163 = 86137904 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 86137904)]) (.cons c98163_0 (.nil)) (by decide) (by decide))

theorem cover98164 : P.CoversSplit 26 10 98164 0xff00ff00ff00fa000000000000000000ff00ff00ff03fa000500050005000000050000000500000005000000050000000500000005010000050000000500000000000000000000000000000000000000000000003300320000000000010000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98164_0 : P.sumLeaves 26 100519936 576 = 611116 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98164) (lo := 0) (len := 576) (W := 611116) check rows elimOK (by decide) (by decide) cover98164 (by decide)
  decide +kernel

theorem contract98164_1 : P.leaf 32 1570633 = 35482 := by
  exact leaf_contract_factors (k := 32) (b := 19) (H := 1570633) (ss := [(2, 1, 482), (21, 0, 1658), (3, 1, 524), (4, 1, 410), (13, 1, 930), (10, 1, 867), (7, 1, 461), (9, 1, 1609), (28, 0, 1658), (30, 0, 1658), (26, 1, 481), (18, 1, 1315), (32, 1, 1315)]) (ids := [3, 4, 6, 9, 10, 12, 13, 14, 15, 17, 18, 20, 22, 23, 25, 27, 29, 31, 21]) (cs := [1, 1, 1, 2, 3, 1, 4, 1, 1, 5, 6, 1, 7, 8, 9, 10, 1, 11, 12, 0, 13, 20, 14, 15, 1, 16, 0, 17, 0, 18, 1, 19]) (bs := [18, 1]) (W := 35482) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c98164_1 : P.sumLeaves 26 100520512 64 = 35482 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1570633) rows (by decide) (by decide)).symm.trans contract98164_1

theorem c98164_2 : P.sumLeaves 26 100520576 384 = 38496346 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98164) (lo := 640) (len := 384) (W := 38496346) check rows elimOK (by decide) (by decide) cover98164 (by decide)
  decide +kernel

theorem h98164 : P.leaf 36 98164 = 39142944 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(576, 611116), (64, 35482), (384, 38496346)]) (.cons c98164_0 (.cons c98164_1 (.cons c98164_2 (.nil)))) (by decide) (by decide))

theorem cover98165 : P.CoversSplit 26 10 98165 0xff00ff00ff00fa000000000000000000ff00ff00ff03fa000500050005000000050000000500000005000000050000000500000005010000050000000500000000000000000000000000000000000000000000003300320000000000010000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98165_0 : P.sumLeaves 26 100520960 1024 = 274082143 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98165) (lo := 0) (len := 1024) (W := 274082143) check rows elimOK (by decide) (by decide) cover98165 (by decide)
  decide +kernel

theorem h98165 : P.leaf 36 98165 = 274082143 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 274082143)]) (.cons c98165_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(98154, 720), (98155, 720), (98156, 720), (98157, 720), (98158, 720), (98159, 720), (98163, 720), (98164, 720), (98165, 720)]

theorem segOK : checkSeg 20 perms 98154 98166 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 98154 98166 6480 2171535740640 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 2171535740640)
    (SegSum.cons (w := 720) h98154 (SegSum.cons (w := 720) h98155 (SegSum.cons (w := 720) h98156 (SegSum.cons (w := 720) h98157 (SegSum.cons (w := 720) h98158 (SegSum.cons (w := 720) h98159 (SegSum.cons (w := 720) h98163 (SegSum.cons (w := 720) h98164 (SegSum.cons (w := 720) h98165 (show SegSum (P.leaf 36) [] 0 from rfl)))))))))) (by decide)

end RACert.S6N0.C0.S75
