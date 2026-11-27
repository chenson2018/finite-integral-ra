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

namespace RACert.S6N0.C0.S67

open RACert RACert.Problem

theorem cover89086 : P.CoversSplit 26 10 89086 0xfffffffffffcfaf8fffffffafffcfaf8fffffffffffcfac8fafafafac8c8c8c8fffffafafffcfaf8fafafafafaf8faf8fffffafafffcfac8fafafafac8c8c8c8ffffffffffccfac8fffffffaffccfac8ffffffffccccc8c8fafafafac8c8c8c80000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [874, 922, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89086_0 : P.sumLeaves 26 91224064 409 = 83532043 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89086) (lo := 0) (len := 409) (W := 83532043) check rows elimOK (by decide) (by decide) cover89086 (by decide)
  decide +kernel

theorem c89086_1 : P.sumLeaves 26 91224473 122 = 205141094 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89086) (lo := 409) (len := 122) (W := 205141094) check rows elimOK (by decide) (by decide) cover89086 (by decide)
  decide +kernel

theorem c89086_2 : P.sumLeaves 26 91224595 132 = 99148178 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89086) (lo := 531) (len := 132) (W := 99148178) check rows elimOK (by decide) (by decide) cover89086 (by decide)
  decide +kernel

theorem c89086_3 : P.sumLeaves 26 91224727 138 = 198358466 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89086) (lo := 663) (len := 138) (W := 198358466) check rows elimOK (by decide) (by decide) cover89086 (by decide)
  decide +kernel

theorem c89086_4 : P.sumLeaves 26 91224865 119 = 195723770 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89086) (lo := 801) (len := 119) (W := 195723770) check rows elimOK (by decide) (by decide) cover89086 (by decide)
  decide +kernel

theorem c89086_5 : P.sumLeaves 26 91224984 104 = 418392108 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89086) (lo := 920) (len := 104) (W := 418392108) check rows elimOK (by decide) (by decide) cover89086 (by decide)
  decide +kernel

theorem h89086 : P.leaf 36 89086 = 1200295659 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(409, 83532043), (122, 205141094), (132, 99148178), (138, 198358466), (119, 195723770), (104, 418392108)]) (.cons c89086_0 (.cons c89086_1 (.cons c89086_2 (.cons c89086_3 (.cons c89086_4 (.cons c89086_5 (.nil))))))) (by decide) (by decide))

theorem cover89087 : P.CoversSplit 26 10 89087 0xfffffffffffcfaf8fffffffafffcfaf8fffffffffffcfac8fafafafac8c8c8c8fffffafafffcfaf8fafafafafaf8faf8fffffafafffcfac8fafafafac8c8c8c8ffffffffffccfac8fffffffaffccfac8ffffffffccccc8c8fafafafac8c8c8c8fffffafaffccfac8fafafafafac8fac8fffffafaccccc8c8fafafafac8c8c8c8 :=
  coversSplit check rows (by decide) (by decide) (xs := [922, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89087_0 : P.sumLeaves 26 91225088 161 = 6906463 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89087) (lo := 0) (len := 161) (W := 6906463) check rows elimOK (by decide) (by decide) cover89087 (by decide)
  decide +kernel

theorem c89087_1 : P.sumLeaves 26 91225249 142 = 93206700 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89087) (lo := 161) (len := 142) (W := 93206700) check rows elimOK (by decide) (by decide) cover89087 (by decide)
  decide +kernel

theorem c89087_2 : P.sumLeaves 26 91225391 131 = 411569952 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89087) (lo := 303) (len := 131) (W := 411569952) check rows elimOK (by decide) (by decide) cover89087 (by decide)
  decide +kernel

theorem c89087_3 : P.sumLeaves 26 91225522 133 = 506583636 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89087) (lo := 434) (len := 133) (W := 506583636) check rows elimOK (by decide) (by decide) cover89087 (by decide)
  decide +kernel

theorem c89087_4 : P.sumLeaves 26 91225655 127 = 419032581 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89087) (lo := 567) (len := 127) (W := 419032581) check rows elimOK (by decide) (by decide) cover89087 (by decide)
  decide +kernel

theorem c89087_5 : P.sumLeaves 26 91225782 137 = 616734642 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89087) (lo := 694) (len := 137) (W := 616734642) check rows elimOK (by decide) (by decide) cover89087 (by decide)
  decide +kernel

theorem c89087_6 : P.sumLeaves 26 91225919 114 = 740365101 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89087) (lo := 831) (len := 114) (W := 740365101) check rows elimOK (by decide) (by decide) cover89087 (by decide)
  decide +kernel

theorem c89087_7 : P.sumLeaves 26 91226033 79 = 825235947 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89087) (lo := 945) (len := 79) (W := 825235947) check rows elimOK (by decide) (by decide) cover89087 (by decide)
  decide +kernel

theorem h89087 : P.leaf 36 89087 = 3619635022 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(161, 6906463), (142, 93206700), (131, 411569952), (133, 506583636), (127, 419032581), (137, 616734642), (114, 740365101), (79, 825235947)]) (.cons c89087_0 (.cons c89087_1 (.cons c89087_2 (.cons c89087_3 (.cons c89087_4 (.cons c89087_5 (.cons c89087_6 (.cons c89087_7 (.nil))))))))) (by decide) (by decide))

theorem cover89559 : P.CoversSplit 26 10 89559 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 531, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89559_0 : P.sumLeaves 26 91708416 1024 = 5504977 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89559) (lo := 0) (len := 1024) (W := 5504977) check rows elimOK (by decide) (by decide) cover89559 (by decide)
  decide +kernel

theorem h89559 : P.leaf 36 89559 = 5504977 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5504977)]) (.cons c89559_0 (.nil)) (by decide) (by decide))

theorem cover89564 : P.CoversSplit 26 10 89564 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 922, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89564_0 : P.sumLeaves 26 91713536 1024 = 4869108 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89564) (lo := 0) (len := 1024) (W := 4869108) check rows elimOK (by decide) (by decide) cover89564 (by decide)
  decide +kernel

theorem h89564 : P.leaf 36 89564 = 4869108 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4869108)]) (.cons c89564_0 (.nil)) (by decide) (by decide))

theorem cover89565 : P.CoversSplit 26 10 89565 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 922, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89565_0 : P.sumLeaves 26 91714560 1024 = 6104773 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89565) (lo := 0) (len := 1024) (W := 6104773) check rows elimOK (by decide) (by decide) cover89565 (by decide)
  decide +kernel

theorem h89565 : P.leaf 36 89565 = 6104773 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6104773)]) (.cons c89565_0 (.nil)) (by decide) (by decide))

theorem cover89567 : P.CoversSplit 26 10 89567 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89567_0 : P.sumLeaves 26 91716608 1024 = 8011129 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89567) (lo := 0) (len := 1024) (W := 8011129) check rows elimOK (by decide) (by decide) cover89567 (by decide)
  decide +kernel

theorem h89567 : P.leaf 36 89567 = 8011129 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8011129)]) (.cons c89567_0 (.nil)) (by decide) (by decide))

theorem cover89580 : P.CoversSplit 26 10 89580 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89580_0 : P.sumLeaves 26 91729920 1024 = 7114308 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89580) (lo := 0) (len := 1024) (W := 7114308) check rows elimOK (by decide) (by decide) cover89580 (by decide)
  decide +kernel

theorem h89580 : P.leaf 36 89580 = 7114308 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 7114308)]) (.cons c89580_0 (.nil)) (by decide) (by decide))

theorem cover89581 : P.CoversSplit 26 10 89581 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89581_0 : P.sumLeaves 26 91730944 1024 = 7246938 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89581) (lo := 0) (len := 1024) (W := 7246938) check rows elimOK (by decide) (by decide) cover89581 (by decide)
  decide +kernel

theorem h89581 : P.leaf 36 89581 = 7246938 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 7246938)]) (.cons c89581_0 (.nil)) (by decide) (by decide))

theorem cover89582 : P.CoversSplit 26 10 89582 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89582_0 : P.sumLeaves 26 91731968 1024 = 8130078 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89582) (lo := 0) (len := 1024) (W := 8130078) check rows elimOK (by decide) (by decide) cover89582 (by decide)
  decide +kernel

theorem h89582 : P.leaf 36 89582 = 8130078 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8130078)]) (.cons c89582_0 (.nil)) (by decide) (by decide))

theorem cover89583 : P.CoversSplit 26 10 89583 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89583_0 : P.sumLeaves 26 91732992 1024 = 8439249 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89583) (lo := 0) (len := 1024) (W := 8439249) check rows elimOK (by decide) (by decide) cover89583 (by decide)
  decide +kernel

theorem h89583 : P.leaf 36 89583 = 8439249 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8439249)]) (.cons c89583_0 (.nil)) (by decide) (by decide))

theorem cover89598 : P.CoversSplit 26 10 89598 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89598_0 : P.sumLeaves 26 91748352 1024 = 10934084 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89598) (lo := 0) (len := 1024) (W := 10934084) check rows elimOK (by decide) (by decide) cover89598 (by decide)
  decide +kernel

theorem h89598 : P.leaf 36 89598 = 10934084 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 10934084)]) (.cons c89598_0 (.nil)) (by decide) (by decide))

theorem cover89599 : P.CoversSplit 26 10 89599 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89599_0 : P.sumLeaves 26 91749376 1024 = 11570142 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89599) (lo := 0) (len := 1024) (W := 11570142) check rows elimOK (by decide) (by decide) cover89599 (by decide)
  decide +kernel

theorem h89599 : P.leaf 36 89599 = 11570142 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 11570142)]) (.cons c89599_0 (.nil)) (by decide) (by decide))

theorem cover89726 : P.CoversSplit 26 10 89726 0xfffffffffffcfaf800000000000000000000000000000000000000000f0c0a080f0f0a0a0f0c0a080f0f0a0a0f0c0a080000000000000000000000000f0c0a0800000000ffccfac8000000000000000000000000ffccfac8000000000f0c0a080000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 587, 874, 979, 1315, 1658, 1665]) (by decide +kernel)

theorem c89726_0 : P.sumLeaves 26 91879424 754 = 10286836 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89726) (lo := 0) (len := 754) (W := 10286836) check rows elimOK (by decide) (by decide) cover89726 (by decide)
  decide +kernel

theorem c89726_1 : P.sumLeaves 26 91880178 270 = 30419636 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89726) (lo := 754) (len := 270) (W := 30419636) check rows elimOK (by decide) (by decide) cover89726 (by decide)
  decide +kernel

theorem h89726 : P.leaf 36 89726 = 40706472 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(754, 10286836), (270, 30419636)]) (.cons c89726_0 (.cons c89726_1 (.nil))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(89086, 360), (89087, 360), (89559, 90), (89564, 360), (89565, 720), (89567, 360), (89580, 360), (89581, 360), (89582, 720), (89583, 720), (89598, 360), (89599, 360), (89726, 120)]

theorem segOK : checkSeg 20 perms 89086 89727 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 89086 89727 5250 1774789076970 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1774789076970)
    (SegSum.cons (w := 360) h89086 (SegSum.cons (w := 360) h89087 (SegSum.cons (w := 90) h89559 (SegSum.cons (w := 360) h89564 (SegSum.cons (w := 720) h89565 (SegSum.cons (w := 360) h89567 (SegSum.cons (w := 360) h89580 (SegSum.cons (w := 360) h89581 (SegSum.cons (w := 720) h89582 (SegSum.cons (w := 720) h89583 (SegSum.cons (w := 360) h89598 (SegSum.cons (w := 360) h89599 (SegSum.cons (w := 120) h89726 (show SegSum (P.leaf 36) [] 0 from rfl)))))))))))))) (by decide)

end RACert.S6N0.C0.S67
