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

namespace RACert.S6N0.C0.S72

open RACert RACert.Problem

theorem cover97269 : P.CoversSplit 26 10 97269 0xff00ff00ff00fa00ff00ff00ff00fa00ff00ff00ff03fa00fa00fa00fa00fa00ff00fa00ff00fa00fa00f000fa00f000ff00fa00ff03fa00fa00f000fa00f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 923, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97269_0 : P.sumLeaves 26 99603456 766 = 103713584 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97269) (lo := 0) (len := 766) (W := 103713584) check rows elimOK (by decide) (by decide) cover97269 (by decide)
  decide +kernel

theorem c97269_1 : P.sumLeaves 26 99604222 220 = 253398824 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97269) (lo := 766) (len := 220) (W := 253398824) check rows elimOK (by decide) (by decide) cover97269 (by decide)
  decide +kernel

theorem c97269_2 : P.sumLeaves 26 99604442 38 = 121580610 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97269) (lo := 986) (len := 38) (W := 121580610) check rows elimOK (by decide) (by decide) cover97269 (by decide)
  decide +kernel

theorem h97269 : P.leaf 36 97269 = 478693018 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(766, 103713584), (220, 253398824), (38, 121580610)]) (.cons c97269_0 (.cons c97269_1 (.cons c97269_2 (.nil)))) (by decide) (by decide))

theorem cover97271 : P.CoversSplit 26 10 97271 0xff00ff00ff00fa00ff00ff00ff00fa00ff00ff00ff03fa00fa00fa00fa00fa00ff00fa00ff00fa00fa00f000fa00f000ff00fa00ff03fa00fa00f000fa00f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f97271 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (99605504 + i)

theorem c97271_0 : rowSum f97271 0 872 = 520753771 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 97271) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover97271 (by decide)
  decide +kernel

theorem c97271_1 : rowSum f97271 872 152 = 542507956 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 97271) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover97271 (by decide)
  decide +kernel

theorem sum97271 : rowSum f97271 0 1024 = 1063261727 :=
  rowSum_append (F := f97271) (lo := 0) (n := 872) (m := 152) (A := 520753771) (B := 542507956) c97271_0 (c97271_1)

theorem h97271 : P.leaf 36 97271 = 1063261727 :=
  leaf_weighted (k := 26) (d := 10) (H := 97271) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 97271) (by decide) (by decide +kernel)) sum97271

theorem cover97272 : P.CoversSplit 26 10 97272 0xf0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f0f0f0f0f0f0f0f0c0f0f0f0f0f0c0f0c00000000000000000000050500000505000000000000000000000505000005040f0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f0f0f0f0f0c000c000f0f0f0f0c000c0000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 874, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f97272 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (99606528 + i)

theorem c97272_0 : rowSum f97272 0 821 = 37133201 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 97272) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover97272 (by decide)
  decide +kernel

theorem c97272_1 : rowSum f97272 821 203 = 56826301 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 97272) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover97272 (by decide)
  decide +kernel

theorem sum97272 : rowSum f97272 0 1024 = 93959502 :=
  rowSum_append (F := f97272) (lo := 0) (n := 821) (m := 203) (A := 37133201) (B := 56826301) c97272_0 (c97272_1)

theorem h97272 : P.leaf 36 97272 = 93959502 :=
  leaf_weighted (k := 26) (d := 10) (H := 97272) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 97272) (by decide) (by decide +kernel)) sum97272

theorem cover97273 : P.CoversSplit 26 10 97273 0xf0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f0f0f0f0f0f0f0f0c0f0f0f0f0f0c0f0c00000000000000000000050500000505000000000000000000000505000005040f0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f0f0f0f0f0c000c000f0f0f0f0c000c0000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 923, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97273_0 : P.sumLeaves 26 99607552 494 = 82528991 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97273) (lo := 0) (len := 494) (W := 82528991) check rows elimOK (by decide) (by decide) cover97273 (by decide)
  decide +kernel

theorem c97273_1 : P.sumLeaves 26 99608046 431 = 166922687 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97273) (lo := 494) (len := 431) (W := 166922687) check rows elimOK (by decide) (by decide) cover97273 (by decide)
  decide +kernel

theorem c97273_2 : P.sumLeaves 26 99608477 99 = 214550566 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97273) (lo := 925) (len := 99) (W := 214550566) check rows elimOK (by decide) (by decide) cover97273 (by decide)
  decide +kernel

theorem h97273 : P.leaf 36 97273 = 464002244 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(494, 82528991), (431, 166922687), (99, 214550566)]) (.cons c97273_0 (.cons c97273_1 (.cons c97273_2 (.nil)))) (by decide) (by decide))

theorem cover97275 : P.CoversSplit 26 10 97275 0xf0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f0f0f0f0f0f0f0f0c0f0f0f0f0f0c0f0c00000000000000000000050500000505000000000000000000000505000005040f0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f0f0f0f0f0c000c000f0f0f0f0c000c0000000000000000000000050500000505000000000000000000000505000004000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f97275 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (99609600 + i)

theorem c97275_0 : rowSum f97275 0 804 = 314255629 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 97275) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover97275 (by decide)
  decide +kernel

theorem c97275_1 : rowSum f97275 804 220 = 793922057 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 97275) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover97275 (by decide)
  decide +kernel

theorem sum97275 : rowSum f97275 0 1024 = 1108177686 :=
  rowSum_append (F := f97275) (lo := 0) (n := 804) (m := 220) (A := 314255629) (B := 793922057) c97275_0 (c97275_1)

theorem h97275 : P.leaf 36 97275 = 1108177686 :=
  leaf_weighted (k := 26) (d := 10) (H := 97275) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 97275) (by decide) (by decide +kernel)) sum97275

theorem cover97276 : P.CoversSplit 26 10 97276 0xfffffffffffffafafffffffafffffafafffffffffffcfac8fafafafafac8fac8fffffafafffffafafafafafafafafafafffffafafffcfac8fafafafafac8fac8fffffffffffffafafffffffafffffafaffffffffccccc8c8fafafafac8c8c8c80000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [874, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f97276 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (99610624 + i)

theorem c97276_0 : rowSum f97276 0 438 = 101617956 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 97276) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover97276 (by decide)
  decide +kernel

theorem c97276_1 : rowSum f97276 438 188 = 165836455 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 97276) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover97276 (by decide)
  decide +kernel

theorem c97276_2 : rowSum f97276 626 224 = 228546976 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 97276) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover97276 (by decide)
  decide +kernel

theorem c97276_3 : rowSum f97276 850 174 = 433795934 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 97276) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover97276 (by decide)
  decide +kernel

theorem sum97276 : rowSum f97276 0 1024 = 929797321 :=
  rowSum_append (F := f97276) (lo := 0) (n := 438) (m := 586) (A := 101617956) (B := 828179365) c97276_0 (rowSum_append (F := f97276) (lo := 438) (n := 188) (m := 398) (A := 165836455) (B := 662342910) c97276_1 (rowSum_append (F := f97276) (lo := 626) (n := 224) (m := 174) (A := 228546976) (B := 433795934) c97276_2 (c97276_3)))

theorem h97276 : P.leaf 36 97276 = 929797321 :=
  leaf_weighted (k := 26) (d := 10) (H := 97276) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 97276) (by decide) (by decide +kernel)) sum97276

theorem cover97277 : P.CoversSplit 26 10 97277 0xfffffffffffffafafffffffafffffafafffffffffffcfac8fafafafafac8fac8fffffafafffffafafafafafafafafafafffffafafffcfac8fafafafafac8fac8fffffffffffffafafffffffafffffafaffffffffccccc8c8fafafafac8c8c8c80000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [923, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97277_0 : P.sumLeaves 26 99611648 402 = 132713370 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97277) (lo := 0) (len := 402) (W := 132713370) check rows elimOK (by decide) (by decide) cover97277 (by decide)
  decide +kernel

theorem c97277_1 : P.sumLeaves 26 99612050 102 = 275691909 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97277) (lo := 402) (len := 102) (W := 275691909) check rows elimOK (by decide) (by decide) cover97277 (by decide)
  decide +kernel

theorem c97277_2 : P.sumLeaves 26 99612152 131 = 199880229 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97277) (lo := 504) (len := 131) (W := 199880229) check rows elimOK (by decide) (by decide) cover97277 (by decide)
  decide +kernel

theorem c97277_3 : P.sumLeaves 26 99612283 120 = 256007510 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97277) (lo := 635) (len := 120) (W := 256007510) check rows elimOK (by decide) (by decide) cover97277 (by decide)
  decide +kernel

theorem c97277_4 : P.sumLeaves 26 99612403 127 = 361001368 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97277) (lo := 755) (len := 127) (W := 361001368) check rows elimOK (by decide) (by decide) cover97277 (by decide)
  decide +kernel

theorem c97277_5 : P.sumLeaves 26 99612530 106 = 512938940 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97277) (lo := 882) (len := 106) (W := 512938940) check rows elimOK (by decide) (by decide) cover97277 (by decide)
  decide +kernel

theorem c97277_6 : P.sumLeaves 26 99612636 36 = 366870608 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97277) (lo := 988) (len := 36) (W := 366870608) check rows elimOK (by decide) (by decide) cover97277 (by decide)
  decide +kernel

theorem h97277 : P.leaf 36 97277 = 2105103934 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(402, 132713370), (102, 275691909), (131, 199880229), (120, 256007510), (127, 361001368), (106, 512938940), (36, 366870608)]) (.cons c97277_0 (.cons c97277_1 (.cons c97277_2 (.cons c97277_3 (.cons c97277_4 (.cons c97277_5 (.cons c97277_6 (.nil)))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(97269, 720), (97271, 360), (97272, 360), (97273, 720), (97275, 360), (97276, 360), (97277, 720)]

theorem segOK : checkSeg 20 perms 97269 97279 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 97269 97279 3600 3344686066080 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 3344686066080)
    (SegSum.cons (w := 720) h97269 (SegSum.cons (w := 360) h97271 (SegSum.cons (w := 360) h97272 (SegSum.cons (w := 720) h97273 (SegSum.cons (w := 360) h97275 (SegSum.cons (w := 360) h97276 (SegSum.cons (w := 720) h97277 (show SegSum (P.leaf 36) [] 0 from rfl)))))))) (by decide)

end RACert.S6N0.C0.S72
