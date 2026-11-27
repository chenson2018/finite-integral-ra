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

namespace RACert.S6N0.C0.S39

open RACert RACert.Problem

theorem cover32759 : P.CoversSplit 26 10 32759 0xff00ff00ff00fa00ff00fa00ff00fa00ff00ff00ff00fa00fa00fa00fa00fa00ff00fa00ff00fa00fa00f000fa00f000ff00fa00ff00fa00fa00f000fa00f00000000000000000000000000000000000000000003300320000000000320032000000000000000000000000000000000000000000330032000000000032003000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 972, 979, 1265, 1273, 1315, 1658]) (by decide +kernel)

theorem c32759_0 : P.sumLeaves 26 33545216 717 = 171660490 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32759) (lo := 0) (len := 717) (W := 171660490) check rows elimOK (by decide) (by decide) cover32759 (by decide)
  decide +kernel

theorem c32759_1 : P.sumLeaves 26 33545933 224 = 402383234 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32759) (lo := 717) (len := 224) (W := 402383234) check rows elimOK (by decide) (by decide) cover32759 (by decide)
  decide +kernel

theorem c32759_2 : P.sumLeaves 26 33546157 83 = 266530620 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32759) (lo := 941) (len := 83) (W := 266530620) check rows elimOK (by decide) (by decide) cover32759 (by decide)
  decide +kernel

theorem h32759 : P.leaf 36 32759 = 840574344 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(717, 171660490), (224, 402383234), (83, 266530620)]) (.cons c32759_0 (.cons c32759_1 (.cons c32759_2 (.nil)))) (by decide) (by decide))

theorem cover32764 : P.CoversSplit 26 10 32764 0xfffffffffffffac8fffffafafffffac8ffffffffffccfac8fac8fac8fac8fac8fffffafafffffac8fafafafafafafac8fffffafaffccfac8fac8fac8fac8fac8ffffffffffccfac8fffffafaffccfac8ffccffccffccfac8fac8fac8fac8fac80000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [874, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c32764_0 : P.sumLeaves 26 33550336 410 = 73088761 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32764) (lo := 0) (len := 410) (W := 73088761) check rows elimOK (by decide) (by decide) cover32764 (by decide)
  decide +kernel

theorem c32764_1 : P.sumLeaves 26 33550746 121 = 152693876 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32764) (lo := 410) (len := 121) (W := 152693876) check rows elimOK (by decide) (by decide) cover32764 (by decide)
  decide +kernel

theorem c32764_2 : P.sumLeaves 26 33550867 140 = 86691471 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32764) (lo := 531) (len := 140) (W := 86691471) check rows elimOK (by decide) (by decide) cover32764 (by decide)
  decide +kernel

theorem c32764_3 : P.sumLeaves 26 33551007 132 = 152908770 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32764) (lo := 671) (len := 132) (W := 152908770) check rows elimOK (by decide) (by decide) cover32764 (by decide)
  decide +kernel

theorem c32764_4 : P.sumLeaves 26 33551139 126 = 175797632 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32764) (lo := 803) (len := 126) (W := 175797632) check rows elimOK (by decide) (by decide) cover32764 (by decide)
  decide +kernel

theorem c32764_5 : P.sumLeaves 26 33551265 95 = 319638858 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32764) (lo := 929) (len := 95) (W := 319638858) check rows elimOK (by decide) (by decide) cover32764 (by decide)
  decide +kernel

theorem h32764 : P.leaf 36 32764 = 960819368 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(410, 73088761), (121, 152693876), (140, 86691471), (132, 152908770), (126, 175797632), (95, 319638858)]) (.cons c32764_0 (.cons c32764_1 (.cons c32764_2 (.cons c32764_3 (.cons c32764_4 (.cons c32764_5 (.nil))))))) (by decide) (by decide))

theorem cover32765 : P.CoversSplit 26 10 32765 0xfffffffffffffac8fffffafafffffac8ffffffffffccfac8fac8fac8fac8fac8fffffafafffffac8fafafafafafafac8fffffafaffccfac8fac8fac8fac8fac8ffffffffffccfac8fffffafaffccfac8ffccffccffccfac8fac8fac8fac8fac80000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [923, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c32765_0 : P.sumLeaves 26 33551360 410 = 188892194 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32765) (lo := 0) (len := 410) (W := 188892194) check rows elimOK (by decide) (by decide) cover32765 (by decide)
  decide +kernel

theorem c32765_1 : P.sumLeaves 26 33551770 121 = 322212046 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32765) (lo := 410) (len := 121) (W := 322212046) check rows elimOK (by decide) (by decide) cover32765 (by decide)
  decide +kernel

theorem c32765_2 : P.sumLeaves 26 33551891 140 = 211380584 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32765) (lo := 531) (len := 140) (W := 211380584) check rows elimOK (by decide) (by decide) cover32765 (by decide)
  decide +kernel

theorem c32765_3 : P.sumLeaves 26 33552031 132 = 339610552 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32765) (lo := 671) (len := 132) (W := 339610552) check rows elimOK (by decide) (by decide) cover32765 (by decide)
  decide +kernel

theorem c32765_4 : P.sumLeaves 26 33552163 126 = 387611000 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32765) (lo := 803) (len := 126) (W := 387611000) check rows elimOK (by decide) (by decide) cover32765 (by decide)
  decide +kernel

theorem c32765_5 : P.sumLeaves 26 33552289 95 = 609106824 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32765) (lo := 929) (len := 95) (W := 609106824) check rows elimOK (by decide) (by decide) cover32765 (by decide)
  decide +kernel

theorem h32765 : P.leaf 36 32765 = 2058813200 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(410, 188892194), (121, 322212046), (140, 211380584), (132, 339610552), (126, 387611000), (95, 609106824)]) (.cons c32765_0 (.cons c32765_1 (.cons c32765_2 (.cons c32765_3 (.cons c32765_4 (.cons c32765_5 (.nil))))))) (by decide) (by decide))

theorem cover32767 : P.CoversSplit 26 10 32767 0xfffffffffffffac8fffffafafffffac8ffffffffffccfac8fac8fac8fac8fac8fffffafafffffac8fafafafafafafac8fffffafaffccfac8fac8fac8fac8fac8ffffffffffccfac8fffffafaffccfac8ffccffccffccfac8fac8fac8fac8fac8fffffafaffccfac8fafafafafac8fac8ffccfac8ffccfac8fac8fac8fac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c32767_0 : P.sumLeaves 26 33553408 161 = 9645663 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32767) (lo := 0) (len := 161) (W := 9645663) check rows elimOK (by decide) (by decide) cover32767 (by decide)
  decide +kernel

theorem c32767_1 : P.sumLeaves 26 33553569 139 = 129127692 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32767) (lo := 161) (len := 139) (W := 129127692) check rows elimOK (by decide) (by decide) cover32767 (by decide)
  decide +kernel

theorem c32767_2 : P.sumLeaves 26 33553708 137 = 592829404 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32767) (lo := 300) (len := 137) (W := 592829404) check rows elimOK (by decide) (by decide) cover32767 (by decide)
  decide +kernel

theorem c32767_3 : P.sumLeaves 26 33553845 135 = 663733356 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32767) (lo := 437) (len := 135) (W := 663733356) check rows elimOK (by decide) (by decide) cover32767 (by decide)
  decide +kernel

theorem c32767_4 : P.sumLeaves 26 33553980 130 = 584597144 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32767) (lo := 572) (len := 130) (W := 584597144) check rows elimOK (by decide) (by decide) cover32767 (by decide)
  decide +kernel

theorem c32767_5 : P.sumLeaves 26 33554110 142 = 907116996 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32767) (lo := 702) (len := 142) (W := 907116996) check rows elimOK (by decide) (by decide) cover32767 (by decide)
  decide +kernel

theorem c32767_6 : P.sumLeaves 26 33554252 111 = 1023692864 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32767) (lo := 844) (len := 111) (W := 1023692864) check rows elimOK (by decide) (by decide) cover32767 (by decide)
  decide +kernel

theorem c32767_7 : P.sumLeaves 26 33554363 69 = 850459488 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32767) (lo := 955) (len := 69) (W := 850459488) check rows elimOK (by decide) (by decide) cover32767 (by decide)
  decide +kernel

theorem h32767 : P.leaf 36 32767 = 4761202607 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(161, 9645663), (139, 129127692), (137, 592829404), (135, 663733356), (130, 584597144), (142, 907116996), (111, 1023692864), (69, 850459488)]) (.cons c32767_0 (.cons c32767_1 (.cons c32767_2 (.cons c32767_3 (.cons c32767_4 (.cons c32767_5 (.cons c32767_6 (.cons c32767_7 (.nil))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(32759, 360), (32764, 180), (32765, 360), (32767, 180)]

theorem segOK : checkSeg 20 perms 32759 65520 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 32759 65520 1080 2073743471340 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 2073743471340)
    (SegSum.cons (w := 360) h32759 (SegSum.cons (w := 180) h32764 (SegSum.cons (w := 360) h32765 (SegSum.cons (w := 180) h32767 (show SegSum (P.leaf 36) [] 0 from rfl))))) (by decide)

end RACert.S6N0.C0.S39
