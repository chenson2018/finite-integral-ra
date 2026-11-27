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

namespace RACert.S6N0.C0.S55

open RACert RACert.Problem

theorem cover79835 : P.CoversSplit 26 10 79835 0xf0f00000f0f00005f0f00000f0f00005f0f00000f0f00000a0a00000a08000000000050500000505000000000000000000000500000000000000000000000000f0f00000f0f00005f0f00000f0f00005f000000000000000a0000000000000000000050500000505000000000000000000000500000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c79835_0 : P.sumLeaves 26 81751040 949 = 12994434 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79835) (lo := 0) (len := 949) (W := 12994434) check rows elimOK (by decide) (by decide) cover79835 (by decide)
  decide +kernel

theorem c79835_1 : P.sumLeaves 26 81751989 75 = 12881856 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79835) (lo := 949) (len := 75) (W := 12881856) check rows elimOK (by decide) (by decide) cover79835 (by decide)
  decide +kernel

theorem h79835 : P.leaf 36 79835 = 25876290 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(949, 12994434), (75, 12881856)]) (.cons c79835_0 (.cons c79835_1 (.nil))) (by decide) (by decide))

theorem cover79836 : P.CoversSplit 26 10 79836 0xffff0000ffff0000ffff0000ffff0000fffc0000fffc0000aaa80000aa880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [467, 880, 923, 979, 1658, 1665]) (by decide +kernel)

theorem c79836_0 : P.sumLeaves 26 81752064 1015 = 28080194 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79836) (lo := 0) (len := 1015) (W := 28080194) check rows elimOK (by decide) (by decide) cover79836 (by decide)
  decide +kernel

theorem c79836_1 : P.sumLeaves 26 81753079 9 = 6245772 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79836) (lo := 1015) (len := 9) (W := 6245772) check rows elimOK (by decide) (by decide) cover79836 (by decide)
  decide +kernel

theorem h79836 : P.leaf 36 79836 = 34325966 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1015, 28080194), (9, 6245772)]) (.cons c79836_0 (.cons c79836_1 (.nil))) (by decide) (by decide))

theorem cover79837 : P.CoversSplit 26 10 79837 0xffff0000ffff0500ffff0000ffff0500fffc0000fffc0000aaa80000aa8800000000000000000000000000000000000000000000000000000000000000000000ffff0000ffff0500ffff0000ffff0500ffcc000000000000aa880000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 923, 930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c79837_0 : P.sumLeaves 26 81753088 827 = 19999994 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79837) (lo := 0) (len := 827) (W := 19999994) check rows elimOK (by decide) (by decide) cover79837 (by decide)
  decide +kernel

theorem c79837_1 : P.sumLeaves 26 81753915 194 = 58366382 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79837) (lo := 827) (len := 194) (W := 58366382) check rows elimOK (by decide) (by decide) cover79837 (by decide)
  decide +kernel

theorem c79837_2 : P.sumLeaves 26 81754109 3 = 4643136 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79837) (lo := 1021) (len := 3) (W := 4643136) check rows elimOK (by decide) (by decide) cover79837 (by decide)
  decide +kernel

theorem h79837 : P.leaf 36 79837 = 83009512 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(827, 19999994), (194, 58366382), (3, 4643136)]) (.cons c79837_0 (.cons c79837_1 (.cons c79837_2 (.nil)))) (by decide) (by decide))

theorem cover79838 : P.CoversSplit 26 10 79838 0xffff0000ffff0500ffff0000ffff0500fffc0000fffc0000aaa80000aa880000050500000505000000000000000000000504000005040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 873, 880, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c79838_0 : P.sumLeaves 26 81754112 981 = 45721306 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79838) (lo := 0) (len := 981) (W := 45721306) check rows elimOK (by decide) (by decide) cover79838 (by decide)
  decide +kernel

theorem c79838_1 : P.sumLeaves 26 81755093 43 = 25231104 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79838) (lo := 981) (len := 43) (W := 25231104) check rows elimOK (by decide) (by decide) cover79838 (by decide)
  decide +kernel

theorem h79838 : P.leaf 36 79838 = 70952410 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(981, 45721306), (43, 25231104)]) (.cons c79838_0 (.cons c79838_1 (.nil))) (by decide) (by decide))

theorem cover79839 : P.CoversSplit 26 10 79839 0xffff0000ffff0500ffff0000ffff0500fffc0000fffc0000aaa80000aa8800000505000005050000000000000000000005040000050400000000000000000000ffff0000ffff0500ffff0000ffff0500ffcc000000000000aa880000000000000505000005050000000000000000000005040000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c79839_0 : P.sumLeaves 26 81755136 511 = 40999781 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79839) (lo := 0) (len := 511) (W := 40999781) check rows elimOK (by decide) (by decide) cover79839 (by decide)
  decide +kernel

theorem c79839_1 : P.sumLeaves 26 81755647 469 = 95846944 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79839) (lo := 511) (len := 469) (W := 95846944) check rows elimOK (by decide) (by decide) cover79839 (by decide)
  decide +kernel

theorem c79839_2 : P.sumLeaves 26 81756116 44 = 51812904 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79839) (lo := 980) (len := 44) (W := 51812904) check rows elimOK (by decide) (by decide) cover79839 (by decide)
  decide +kernel

theorem h79839 : P.leaf 36 79839 = 188659629 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(511, 40999781), (469, 95846944), (44, 51812904)]) (.cons c79839_0 (.cons c79839_1 (.cons c79839_2 (.nil)))) (by decide) (by decide))

theorem cover79852 : P.CoversSplit 26 10 79852 0xfffffffafffffafafffffffafffffafafffcfff8fffcc8c8aaa8aaa8aa888888000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 874, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c79852_0 : P.sumLeaves 26 81768448 925 = 13276868 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79852) (lo := 0) (len := 925) (W := 13276868) check rows elimOK (by decide) (by decide) cover79852 (by decide)
  decide +kernel

theorem c79852_1 : P.sumLeaves 26 81769373 99 = 31369776 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79852) (lo := 925) (len := 99) (W := 31369776) check rows elimOK (by decide) (by decide) cover79852 (by decide)
  decide +kernel

theorem h79852 : P.leaf 36 79852 = 44646644 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(925, 13276868), (99, 31369776)]) (.cons c79852_0 (.cons c79852_1 (.nil))) (by decide) (by decide))

theorem cover79853 : P.CoversSplit 26 10 79853 0xfffffffafffffafafffffffafffffafafffcfff8fffcc8c8aaa8aaa8aa8888880000000000000000000000000000000000000000000000000000000000000000fffffffafffffafafffffffafffffafaffccffc8cc00c800aa88aa88880088000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 923, 930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c79853_0 : P.sumLeaves 26 81769472 440 = 11682074 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79853) (lo := 0) (len := 440) (W := 11682074) check rows elimOK (by decide) (by decide) cover79853 (by decide)
  decide +kernel

theorem c79853_1 : P.sumLeaves 26 81769912 410 = 22798804 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79853) (lo := 440) (len := 410) (W := 22798804) check rows elimOK (by decide) (by decide) cover79853 (by decide)
  decide +kernel

theorem c79853_2 : P.sumLeaves 26 81770322 107 = 33237870 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79853) (lo := 850) (len := 107) (W := 33237870) check rows elimOK (by decide) (by decide) cover79853 (by decide)
  decide +kernel

theorem c79853_3 : P.sumLeaves 26 81770429 67 = 41806740 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79853) (lo := 957) (len := 67) (W := 41806740) check rows elimOK (by decide) (by decide) cover79853 (by decide)
  decide +kernel

theorem h79853 : P.leaf 36 79853 = 109525488 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(440, 11682074), (410, 22798804), (107, 33237870), (67, 41806740)]) (.cons c79853_0 (.cons c79853_1 (.cons c79853_2 (.cons c79853_3 (.nil))))) (by decide) (by decide))

theorem cover79854 : P.CoversSplit 26 10 79854 0xfffffffafffffafafffffffafffffafafffcfff8fffcc8c8aaa8aaa8aa888888000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 874, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c79854_0 : P.sumLeaves 26 81770496 925 = 51097914 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79854) (lo := 0) (len := 925) (W := 51097914) check rows elimOK (by decide) (by decide) cover79854 (by decide)
  decide +kernel

theorem c79854_1 : P.sumLeaves 26 81771421 99 = 102930094 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79854) (lo := 925) (len := 99) (W := 102930094) check rows elimOK (by decide) (by decide) cover79854 (by decide)
  decide +kernel

theorem h79854 : P.leaf 36 79854 = 154028008 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(925, 51097914), (99, 102930094)]) (.cons c79854_0 (.cons c79854_1 (.nil))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(79835, 360), (79836, 720), (79837, 720), (79838, 720), (79839, 720), (79852, 360), (79853, 360), (79854, 720)]

theorem segOK : checkSeg 20 perms 79835 79855 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 79835 79855 4680 447119809920 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 447119809920)
    (SegSum.cons (w := 360) h79835 (SegSum.cons (w := 720) h79836 (SegSum.cons (w := 720) h79837 (SegSum.cons (w := 720) h79838 (SegSum.cons (w := 720) h79839 (SegSum.cons (w := 360) h79852 (SegSum.cons (w := 360) h79853 (SegSum.cons (w := 720) h79854 (show SegSum (P.leaf 36) [] 0 from rfl))))))))) (by decide)

end RACert.S6N0.C0.S55
