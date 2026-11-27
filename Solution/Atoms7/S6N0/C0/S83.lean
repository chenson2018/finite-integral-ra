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

namespace RACert.S6N0.C0.S83

open RACert RACert.Problem

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

theorem c98164_0 : P.sumLeaves 26 100519936 1024 = 39142944 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98164) (lo := 0) (len := 1024) (W := 39142944) check rows elimOK (by decide) (by decide) cover98164 (by decide)
  decide +kernel

theorem h98164 : P.leaf 36 98164 = 39142944 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 39142944)]) (.cons c98164_0 (.nil)) (by decide) (by decide))

theorem cover98165 : P.CoversSplit 26 10 98165 0xff00ff00ff00fa000000000000000000ff00ff00ff03fa000500050005000000050000000500000005000000050000000500000005010000050000000500000000000000000000000000000000000000000000003300320000000000010000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98165_0 : P.sumLeaves 26 100520960 1024 = 274082143 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98165) (lo := 0) (len := 1024) (W := 274082143) check rows elimOK (by decide) (by decide) cover98165 (by decide)
  decide +kernel

theorem h98165 : P.leaf 36 98165 = 274082143 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 274082143)]) (.cons c98165_0 (.nil)) (by decide) (by decide))

theorem cover98166 : P.CoversSplit 26 10 98166 0xff00ff00ff00fa000000000000000000ff00ff00ff03fa000500050005000000050000000500000005000000050000000500000005010000050000000500000000000000000000000000000000000000000000003300320000000000010000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98166_0 : P.sumLeaves 26 100521984 1024 = 321664850 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98166) (lo := 0) (len := 1024) (W := 321664850) check rows elimOK (by decide) (by decide) cover98166 (by decide)
  decide +kernel

theorem h98166 : P.leaf 36 98166 = 321664850 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 321664850)]) (.cons c98166_0 (.nil)) (by decide) (by decide))

theorem cover98167 : P.CoversSplit 26 10 98167 0xff00ff00ff00fa000000000000000000ff00ff00ff03fa000500050005000000050000000500000005000000050000000500000005010000050000000500000000000000000000000000000000000000000000003300320000000000010000000000000000000000000000000000000000000000010000000000000001000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98167_0 : P.sumLeaves 26 100523008 1024 = 527766462 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98167) (lo := 0) (len := 1024) (W := 527766462) check rows elimOK (by decide) (by decide) cover98167 (by decide)
  decide +kernel

theorem h98167 : P.leaf 36 98167 = 527766462 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 527766462)]) (.cons c98167_0 (.nil)) (by decide) (by decide))

theorem cover98169 : P.CoversSplit 26 10 98169 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0c000000005000000000000000000000000000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f000f00000000005000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 579, 923, 972, 979, 1315, 1322, 1658]) (by decide +kernel)

theorem c98169_0 : P.sumLeaves 26 100525056 974 = 125440772 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98169) (lo := 0) (len := 974) (W := 125440772) check rows elimOK (by decide) (by decide) cover98169 (by decide)
  decide +kernel

theorem c98169_1 : P.sumLeaves 26 100526030 50 = 140913628 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98169) (lo := 974) (len := 50) (W := 140913628) check rows elimOK (by decide) (by decide) cover98169 (by decide)
  decide +kernel

theorem h98169 : P.leaf 36 98169 = 266354400 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(974, 125440772), (50, 140913628)]) (.cons c98169_0 (.cons c98169_1 (.nil))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(98156, 720), (98157, 720), (98158, 720), (98159, 720), (98163, 720), (98164, 720), (98165, 720), (98166, 720), (98167, 720), (98169, 720)]

theorem segOK : checkSeg 20 perms 98156 98170 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 98156 98170 7200 2694300283440 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 2694300283440)
    (SegSum.cons (w := 720) h98156 (SegSum.cons (w := 720) h98157 (SegSum.cons (w := 720) h98158 (SegSum.cons (w := 720) h98159 (SegSum.cons (w := 720) h98163 (SegSum.cons (w := 720) h98164 (SegSum.cons (w := 720) h98165 (SegSum.cons (w := 720) h98166 (SegSum.cons (w := 720) h98167 (SegSum.cons (w := 720) h98169 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))) (by decide)

end RACert.S6N0.C0.S83
