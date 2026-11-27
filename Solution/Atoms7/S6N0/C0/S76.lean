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

namespace RACert.S6N0.C0.S76

open RACert RACert.Problem

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

theorem cover98170 : P.CoversSplit 26 10 98170 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0c000000005000000000000000000000000000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f000f00000000005000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 874, 972, 979, 1315, 1322, 1658]) (by decide +kernel)

theorem c98170_0 : P.sumLeaves 26 100526080 974 = 122537866 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98170) (lo := 0) (len := 974) (W := 122537866) check rows elimOK (by decide) (by decide) cover98170 (by decide)
  decide +kernel

theorem c98170_1 : P.sumLeaves 26 100527054 50 = 141104602 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98170) (lo := 974) (len := 50) (W := 141104602) check rows elimOK (by decide) (by decide) cover98170 (by decide)
  decide +kernel

theorem h98170 : P.leaf 36 98170 = 263642468 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(974, 122537866), (50, 141104602)]) (.cons c98170_0 (.cons c98170_1 (.nil))) (by decide) (by decide))

theorem cover98171 : P.CoversSplit 26 10 98171 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0c000000005000000000000000000000000000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f000f00000000005000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 972, 979, 1315, 1322, 1658]) (by decide +kernel)

theorem c98171_0 : P.sumLeaves 26 100527104 974 = 234153122 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98171) (lo := 0) (len := 974) (W := 234153122) check rows elimOK (by decide) (by decide) cover98171 (by decide)
  decide +kernel

theorem c98171_1 : P.sumLeaves 26 100528078 50 = 214526498 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98171) (lo := 974) (len := 50) (W := 214526498) check rows elimOK (by decide) (by decide) cover98171 (by decide)
  decide +kernel

theorem h98171 : P.leaf 36 98171 = 448679620 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(974, 234153122), (50, 214526498)]) (.cons c98171_0 (.cons c98171_1 (.nil))) (by decide) (by decide))

theorem cover98172 : P.CoversSplit 26 10 98172 0xfffffffffffffafa0000000000000000fffffffffffcfac805050500050000000505000005050000050500000505000005050000050400000505000005000000fffffffffffffafa0000000000000000ffffffffff00fa0005050500050000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98172_0 : P.sumLeaves 26 100528128 494 = 91759552 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98172) (lo := 0) (len := 494) (W := 91759552) check rows elimOK (by decide) (by decide) cover98172 (by decide)
  decide +kernel

theorem c98172_1 : P.sumLeaves 26 100528622 388 = 161058740 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98172) (lo := 494) (len := 388) (W := 161058740) check rows elimOK (by decide) (by decide) cover98172 (by decide)
  decide +kernel

theorem c98172_2 : P.sumLeaves 26 100529010 142 = 425377684 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98172) (lo := 882) (len := 142) (W := 425377684) check rows elimOK (by decide) (by decide) cover98172 (by decide)
  decide +kernel

theorem h98172 : P.leaf 36 98172 = 678195976 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(494, 91759552), (388, 161058740), (142, 425377684)]) (.cons c98172_0 (.cons c98172_1 (.cons c98172_2 (.nil)))) (by decide) (by decide))

theorem cover98173 : P.CoversSplit 26 10 98173 0xfffffffffffffafa0000000000000000fffffffffffcfac805050500050000000505000005050000050500000505000005050000050400000505000005000000fffffffffffffafa0000000000000000ffffffffff00fa0005050500050000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98173_0 : P.sumLeaves 26 100529152 494 = 174505196 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98173) (lo := 0) (len := 494) (W := 174505196) check rows elimOK (by decide) (by decide) cover98173 (by decide)
  decide +kernel

theorem c98173_1 : P.sumLeaves 26 100529646 388 = 280114365 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98173) (lo := 494) (len := 388) (W := 280114365) check rows elimOK (by decide) (by decide) cover98173 (by decide)
  decide +kernel

theorem c98173_2 : P.sumLeaves 26 100530034 142 = 642455181 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98173) (lo := 882) (len := 142) (W := 642455181) check rows elimOK (by decide) (by decide) cover98173 (by decide)
  decide +kernel

theorem h98173 : P.leaf 36 98173 = 1097074742 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(494, 174505196), (388, 280114365), (142, 642455181)]) (.cons c98173_0 (.cons c98173_1 (.cons c98173_2 (.nil)))) (by decide) (by decide))

theorem cover98174 : P.CoversSplit 26 10 98174 0xfffffffffffffafa0000000000000000fffffffffffcfac805050500050000000505000005050000050500000505000005050000050400000505000005000000fffffffffffffafa0000000000000000ffffffffff00fa0005050500050000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98174_0 : P.sumLeaves 26 100530176 494 = 159001485 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98174) (lo := 0) (len := 494) (W := 159001485) check rows elimOK (by decide) (by decide) cover98174 (by decide)
  decide +kernel

theorem c98174_1 : P.sumLeaves 26 100530670 388 = 370173568 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98174) (lo := 494) (len := 388) (W := 370173568) check rows elimOK (by decide) (by decide) cover98174 (by decide)
  decide +kernel

theorem c98174_2 : P.sumLeaves 26 100531058 142 = 778020333 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98174) (lo := 882) (len := 142) (W := 778020333) check rows elimOK (by decide) (by decide) cover98174 (by decide)
  decide +kernel

theorem h98174 : P.leaf 36 98174 = 1307195386 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(494, 159001485), (388, 370173568), (142, 778020333)]) (.cons c98174_0 (.cons c98174_1 (.cons c98174_2 (.nil)))) (by decide) (by decide))

theorem cover98175 : P.CoversSplit 26 10 98175 0xfffffffffffffafa0000000000000000fffffffffffcfac805050500050000000505000005050000050500000505000005050000050400000505000005000000fffffffffffffafa0000000000000000ffffffffff00fa0005050500050000000505000005050000050500000505000005050000050000000505000005000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98175_0 : P.sumLeaves 26 100531200 466 = 168500041 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98175) (lo := 0) (len := 466) (W := 168500041) check rows elimOK (by decide) (by decide) cover98175 (by decide)
  decide +kernel

theorem c98175_1 : P.sumLeaves 26 100531666 388 = 393753954 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98175) (lo := 466) (len := 388) (W := 393753954) check rows elimOK (by decide) (by decide) cover98175 (by decide)
  decide +kernel

theorem c98175_2 : P.sumLeaves 26 100532054 164 = 1196432760 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98175) (lo := 854) (len := 164) (W := 1196432760) check rows elimOK (by decide) (by decide) cover98175 (by decide)
  decide +kernel

theorem c98175_3 : P.sumLeaves 26 100532218 6 = 109747722 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98175) (lo := 1018) (len := 6) (W := 109747722) check rows elimOK (by decide) (by decide) cover98175 (by decide)
  decide +kernel

theorem h98175 : P.leaf 36 98175 = 1868434477 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(466, 168500041), (388, 393753954), (164, 1196432760), (6, 109747722)]) (.cons c98175_0 (.cons c98175_1 (.cons c98175_2 (.cons c98175_3 (.nil))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(98166, 720), (98167, 720), (98169, 720), (98170, 720), (98171, 720), (98172, 720), (98173, 720), (98174, 720), (98175, 720)]

theorem segOK : checkSeg 20 perms 98166 98275 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 98166 98275 6480 4880886034320 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 4880886034320)
    (SegSum.cons (w := 720) h98166 (SegSum.cons (w := 720) h98167 (SegSum.cons (w := 720) h98169 (SegSum.cons (w := 720) h98170 (SegSum.cons (w := 720) h98171 (SegSum.cons (w := 720) h98172 (SegSum.cons (w := 720) h98173 (SegSum.cons (w := 720) h98174 (SegSum.cons (w := 720) h98175 (show SegSum (P.leaf 36) [] 0 from rfl)))))))))) (by decide)

end RACert.S6N0.C0.S76
