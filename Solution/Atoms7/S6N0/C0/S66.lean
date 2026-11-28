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

namespace RACert.S6N0.C0.S66

open RACert RACert.Problem

theorem cover604527 : P.CoversSplit 26 10 604527 0xaa00aa0000000000aa00ab0000000000aa00aa0000000002aa00ab0000000002000000000000000000000a0000000000000000000000000000000a000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [531, 579, 629, 636, 930, 972, 979, 1273, 1315, 1322]) (by decide +kernel)

theorem c604527_0 : P.sumLeaves 26 619035648 1024 = 23335469 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 604527) (lo := 0) (len := 1024) (W := 23335469) check rows elimOK (by decide) (by decide) cover604527 (by decide)
  decide +kernel

theorem h604527 : P.leaf 36 604527 = 23335469 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 23335469)]) (.cons c604527_0 (.nil)) (by decide) (by decide))

theorem h98149 : P.leaf 36 98149 = 23335469 :=
  orient93 (v := 604527) (by decide) (by decide +kernel) h604527

theorem cover98150 : P.CoversSplit 26 10 98150 0xff00ff00ff00fa000000000000000000ff00ff00ff03fa000500050005000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003300320000000000010000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 874, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98150_0 : P.sumLeaves 26 100505600 1024 = 185607689 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98150) (lo := 0) (len := 1024) (W := 185607689) check rows elimOK (by decide) (by decide) cover98150 (by decide)
  decide +kernel

theorem h98150 : P.leaf 36 98150 = 185607689 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 185607689)]) (.cons c98150_0 (.nil)) (by decide) (by decide))

theorem cover98151 : P.CoversSplit 26 10 98151 0xff00ff00ff00fa000000000000000000ff00ff00ff03fa000500050005000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003300320000000000010000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98151_0 : P.sumLeaves 26 100506624 1024 = 362491499 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98151) (lo := 0) (len := 1024) (W := 362491499) check rows elimOK (by decide) (by decide) cover98151 (by decide)
  decide +kernel

theorem h98151 : P.leaf 36 98151 = 362491499 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 362491499)]) (.cons c98151_0 (.nil)) (by decide) (by decide))

theorem cover310739 : P.CoversSplit 26 10 310739 0xaa000000aa000000aa000000aa00000000000000000000000000000000000000000000000000000000000a0000000a000000000000000000000000000000000000000000002200000000000000220000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 488, 489, 530, 629, 636, 930, 1665]) (by decide +kernel)

theorem h310739 : P.leaf 36 310739 = 33346056 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 310739) (keep := keep18) (twice := twice18) rows (by decide) (by decide) bal18 (invRow18 (H := 310739) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 310739) (weight := rowWeight keep18 twice18) (xs := [129, 401, 405, 465, 469, 649, 651, 681, 683, 921, 923, 925, 927, 953, 955, 957, 959, 985, 987, 989, 991, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover310739 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h98153 : P.leaf 36 98153 = 33346056 :=
  orient6 (v := 310739) (by decide) (by decide +kernel) h310739

theorem cover311187 : P.CoversSplit 26 10 311187 0xff00cc0000000000ff00c8000000000000000000000000000000000000000000ff00cc0000000000aa0088000000000000000000000000000000000000000000ff00cc0000220000ff00c8000022000000000000000000000000000000000000ff00cc0000220000aa0088000022000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 488, 489, 531, 537, 930, 1272, 1273, 1658]) (by decide +kernel)

theorem c311187_0 : P.sumLeaves 26 318655488 1024 = 119758582 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 311187) (lo := 0) (len := 1024) (W := 119758582) check rows elimOK (by decide) (by decide) cover311187 (by decide)
  decide +kernel

theorem h311187 : P.leaf 36 311187 = 119758582 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 119758582)]) (.cons c311187_0 (.nil)) (by decide) (by decide))

theorem h98154 : P.leaf 36 98154 = 119758582 :=
  orient74 (v := 311187) (by decide) (by decide +kernel) h311187

theorem cover311191 : P.CoversSplit 26 10 311191 0xff00cc0000000000ff00c8000000000000000000000000000000000000000000ff00cc0000000000aa0088000000000000000000000000000000000000000000ff00cc0000330000ff00c8000033000000000000000000000000000000000000ff00cc0000330000aa0088000022000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 531, 538, 930, 1272, 1273, 1658]) (by decide +kernel)

theorem c311191_0 : P.sumLeaves 26 318659584 1024 = 269965265 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 311191) (lo := 0) (len := 1024) (W := 269965265) check rows elimOK (by decide) (by decide) cover311191 (by decide)
  decide +kernel

theorem h311191 : P.leaf 36 311191 = 269965265 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 269965265)]) (.cons c311191_0 (.nil)) (by decide) (by decide))

theorem h98155 : P.leaf 36 98155 = 269965265 :=
  orient74 (v := 311191) (by decide) (by decide +kernel) h311191

theorem cover310746 : P.CoversSplit 26 10 310746 0xaaaa0000aaaa0000aaaa0000aaaa000000000000000000000000000000000000000000000000000000000a0a00000a0a0000000000000000000000000000000000220000002200000022000000220000000000000000000000000000000000000000000000000000000000020000000200000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 629, 636, 1272, 1665]) (by decide +kernel)

theorem c310746_0 : P.sumLeaves 26 318203904 1024 = 89951884 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 310746) (lo := 0) (len := 1024) (W := 89951884) check rows elimOK (by decide) (by decide) cover310746 (by decide)
  decide +kernel

theorem h310746 : P.leaf 36 310746 = 89951884 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 89951884)]) (.cons c310746_0 (.nil)) (by decide) (by decide))

theorem h98156 : P.leaf 36 98156 = 89951884 :=
  orient6 (v := 310746) (by decide) (by decide +kernel) h310746

theorem cover310747 : P.CoversSplit 26 10 310747 0xaaaa0000aaaa0000aaaa0000aaaa000000000000000000000000000000000000000000000000000000000a0a00000a0a0000000000000000000000000000000000220000002200000022000000220000000000000000000000000000000000000000000000000000000000020000000200000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 629, 636, 1272, 1665]) (by decide +kernel)

theorem c310747_0 : P.sumLeaves 26 318204928 1024 = 176620103 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 310747) (lo := 0) (len := 1024) (W := 176620103) check rows elimOK (by decide) (by decide) cover310747 (by decide)
  decide +kernel

theorem h310747 : P.leaf 36 310747 = 176620103 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 176620103)]) (.cons c310747_0 (.nil)) (by decide) (by decide))

theorem h98157 : P.leaf 36 98157 = 176620103 :=
  orient6 (v := 310747) (by decide) (by decide +kernel) h310747

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

theorem cover356845 : P.CoversSplit 26 10 356845 0xf0f0f0f0f0f0f0f0f0f0f0f4f0f0f0f400000000000000000000000000200020000000000000000000005050000050500000000000000000000000000000000000000000003000300000000000300030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [580, 629, 636, 873, 972, 979, 1273, 1658, 1665]) (by decide +kernel)

theorem c356845_0 : P.sumLeaves 26 365409280 1024 = 39142944 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 356845) (lo := 0) (len := 1024) (W := 39142944) check rows elimOK (by decide) (by decide) cover356845 (by decide)
  decide +kernel

theorem h356845 : P.leaf 36 356845 = 39142944 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 39142944)]) (.cons c356845_0 (.nil)) (by decide) (by decide))

theorem h98164 : P.leaf 36 98164 = 39142944 :=
  orient348 (v := 356845) (by decide) (by decide +kernel) h356845

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

def seg : List (ℕ × ℕ) := [(98149, 720), (98150, 720), (98151, 720), (98153, 360), (98154, 720), (98155, 720), (98156, 720), (98157, 720), (98158, 720), (98159, 720), (98163, 720), (98164, 720), (98165, 720), (98166, 720), (98167, 720), (98169, 720)]

theorem segOK : checkSeg 20 perms 98149 98170 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 98149 98170 11160 3398338986480 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 3398338986480)
    (SegSum.cons (w := 720) h98149 (SegSum.cons (w := 720) h98150 (SegSum.cons (w := 720) h98151 (SegSum.cons (w := 360) h98153 (SegSum.cons (w := 720) h98154 (SegSum.cons (w := 720) h98155 (SegSum.cons (w := 720) h98156 (SegSum.cons (w := 720) h98157 (SegSum.cons (w := 720) h98158 (SegSum.cons (w := 720) h98159 (SegSum.cons (w := 720) h98163 (SegSum.cons (w := 720) h98164 (SegSum.cons (w := 720) h98165 (SegSum.cons (w := 720) h98166 (SegSum.cons (w := 720) h98167 (SegSum.cons (w := 720) h98169 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))) (by decide)

end RACert.S6N0.C0.S66
