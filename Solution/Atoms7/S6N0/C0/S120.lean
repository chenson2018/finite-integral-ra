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

namespace RACert.S6N0.C0.S120

open RACert RACert.Problem

theorem cover242479 : P.CoversSplit 26 10 242479 0xfffffffffffffffffffffffffffff0f0ffffffffffffccccffffaaaaff008000fffffafafffffafafafaa0a0fafaa0a0fffffafaffffc8c8fafaa0a0fa008000ffffffffffccffccffffffffffccf0c0ffccffcccc00cc00ffccaa88cc0080000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 579, 873, 930, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c242479_0 : P.sumLeaves 26 248298496 439 = 80990433 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242479) (lo := 0) (len := 439) (W := 80990433) check rows elimOK (by decide) (by decide) cover242479 (by decide)
  decide +kernel

theorem c242479_1 : P.sumLeaves 26 248298935 155 = 134374603 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242479) (lo := 439) (len := 155) (W := 134374603) check rows elimOK (by decide) (by decide) cover242479 (by decide)
  decide +kernel

theorem c242479_2 : P.sumLeaves 26 248299090 136 = 99090622 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242479) (lo := 594) (len := 136) (W := 99090622) check rows elimOK (by decide) (by decide) cover242479 (by decide)
  decide +kernel

theorem c242479_3 : P.sumLeaves 26 248299226 139 = 129459915 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242479) (lo := 730) (len := 139) (W := 129459915) check rows elimOK (by decide) (by decide) cover242479 (by decide)
  decide +kernel

theorem c242479_4 : P.sumLeaves 26 248299365 104 = 118161383 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242479) (lo := 869) (len := 104) (W := 118161383) check rows elimOK (by decide) (by decide) cover242479 (by decide)
  decide +kernel

theorem c242479_5 : P.sumLeaves 26 248299469 51 = 118673826 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242479) (lo := 973) (len := 51) (W := 118673826) check rows elimOK (by decide) (by decide) cover242479 (by decide)
  decide +kernel

theorem h242479 : P.leaf 36 242479 = 680750782 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(439, 80990433), (155, 134374603), (136, 99090622), (139, 129459915), (104, 118161383), (51, 118673826)]) (.cons c242479_0 (.cons c242479_1 (.cons c242479_2 (.cons c242479_3 (.cons c242479_4 (.cons c242479_5 (.nil))))))) (by decide) (by decide))

theorem cover242487 : P.CoversSplit 26 10 242487 0xfffffffffffffffffffffffffffff0f0ffffffffffffccccffffaaaaff008000fffffafafffffafaffffa0a0ffffa0a0fffffafaffffc8c8ffffa0a0ff008000fffffffffffffffffffffffffffff0f0ffccffcccc00cc00ffccaa88cc008000fffffafafffffafaffffa0a0ffffa0a0ffccfac8cc00c800ffcca080cc008000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 873, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c242487_0 : P.sumLeaves 26 248306688 204 = 21890839 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242487) (lo := 0) (len := 204) (W := 21890839) check rows elimOK (by decide) (by decide) cover242487 (by decide)
  decide +kernel

theorem c242487_1 : P.sumLeaves 26 248306892 173 = 74264236 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242487) (lo := 204) (len := 173) (W := 74264236) check rows elimOK (by decide) (by decide) cover242487 (by decide)
  decide +kernel

theorem c242487_2 : P.sumLeaves 26 248307065 104 = 91879749 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242487) (lo := 377) (len := 104) (W := 91879749) check rows elimOK (by decide) (by decide) cover242487 (by decide)
  decide +kernel

theorem c242487_3 : P.sumLeaves 26 248307169 145 = 116492730 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242487) (lo := 481) (len := 145) (W := 116492730) check rows elimOK (by decide) (by decide) cover242487 (by decide)
  decide +kernel

theorem c242487_4 : P.sumLeaves 26 248307314 128 = 87882727 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242487) (lo := 626) (len := 128) (W := 87882727) check rows elimOK (by decide) (by decide) cover242487 (by decide)
  decide +kernel

theorem c242487_5 : P.sumLeaves 26 248307442 135 = 126068331 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242487) (lo := 754) (len := 135) (W := 126068331) check rows elimOK (by decide) (by decide) cover242487 (by decide)
  decide +kernel

theorem c242487_6 : P.sumLeaves 26 248307577 104 = 115403698 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242487) (lo := 889) (len := 104) (W := 115403698) check rows elimOK (by decide) (by decide) cover242487 (by decide)
  decide +kernel

theorem c242487_7 : P.sumLeaves 26 248307681 31 = 85770132 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242487) (lo := 993) (len := 31) (W := 85770132) check rows elimOK (by decide) (by decide) cover242487 (by decide)
  decide +kernel

theorem h242487 : P.leaf 36 242487 = 719652442 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(204, 21890839), (173, 74264236), (104, 91879749), (145, 116492730), (128, 87882727), (135, 126068331), (104, 115403698), (31, 85770132)]) (.cons c242487_0 (.cons c242487_1 (.cons c242487_2 (.cons c242487_3 (.cons c242487_4 (.cons c242487_5 (.cons c242487_6 (.cons c242487_7 (.nil))))))))) (by decide) (by decide))

theorem cover242495 : P.CoversSplit 26 10 242495 0xfffffffffffffffffffffffffffff0f0ffffffffffffccccffffaaaaff008000fffffafafffffafaffffa0a0ffffa0a0fffffafaffffc8c8ffffa0a0ff008000fffffffffffffffffffffffffffff0f0ffccffcccc00cc00ffccaa88cc008000fffffafafffffafaffffa0a0ffffa0a0ffccfac8cc00c800ffcca080cc008000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 579, 873, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c242495_0 : P.sumLeaves 26 248314880 204 = 81270623 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242495) (lo := 0) (len := 204) (W := 81270623) check rows elimOK (by decide) (by decide) cover242495 (by decide)
  decide +kernel

theorem c242495_1 : P.sumLeaves 26 248315084 173 = 157147598 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242495) (lo := 204) (len := 173) (W := 157147598) check rows elimOK (by decide) (by decide) cover242495 (by decide)
  decide +kernel

theorem c242495_2 : P.sumLeaves 26 248315257 104 = 156954765 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242495) (lo := 377) (len := 104) (W := 156954765) check rows elimOK (by decide) (by decide) cover242495 (by decide)
  decide +kernel

theorem c242495_3 : P.sumLeaves 26 248315361 145 = 219066900 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242495) (lo := 481) (len := 145) (W := 219066900) check rows elimOK (by decide) (by decide) cover242495 (by decide)
  decide +kernel

theorem c242495_4 : P.sumLeaves 26 248315506 128 = 197792220 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242495) (lo := 626) (len := 128) (W := 197792220) check rows elimOK (by decide) (by decide) cover242495 (by decide)
  decide +kernel

theorem c242495_5 : P.sumLeaves 26 248315634 135 = 228837329 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242495) (lo := 754) (len := 135) (W := 228837329) check rows elimOK (by decide) (by decide) cover242495 (by decide)
  decide +kernel

theorem c242495_6 : P.sumLeaves 26 248315769 104 = 208899730 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242495) (lo := 889) (len := 104) (W := 208899730) check rows elimOK (by decide) (by decide) cover242495 (by decide)
  decide +kernel

theorem c242495_7 : P.sumLeaves 26 248315873 31 = 149448754 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242495) (lo := 993) (len := 31) (W := 149448754) check rows elimOK (by decide) (by decide) cover242495 (by decide)
  decide +kernel

theorem h242495 : P.leaf 36 242495 = 1399417919 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(204, 81270623), (173, 157147598), (104, 156954765), (145, 219066900), (128, 197792220), (135, 228837329), (104, 208899730), (31, 149448754)]) (.cons c242495_0 (.cons c242495_1 (.cons c242495_2 (.cons c242495_3 (.cons c242495_4 (.cons c242495_5 (.cons c242495_6 (.cons c242495_7 (.nil))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(242479, 180), (242487, 360), (242495, 360)]

theorem segOK : checkSeg 20 perms 242479 242543 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 242479 242543 900 885400470720 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 885400470720)
    (SegSum.cons (w := 180) h242479 (SegSum.cons (w := 360) h242487 (SegSum.cons (w := 360) h242495 (show SegSum (P.leaf 36) [] 0 from rfl)))) (by decide)

end RACert.S6N0.C0.S120
