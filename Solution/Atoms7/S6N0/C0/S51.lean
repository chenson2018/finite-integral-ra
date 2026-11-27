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

namespace RACert.S6N0.C0.S51

open RACert RACert.Problem

theorem cover79835 : P.CoversSplit 26 10 79835 0xf0f00000f0f00005f0f00000f0f00005f0f00000f0f00000a0a00000a08000000000050500000505000000000000000000000500000000000000000000000000f0f00000f0f00005f0f00000f0f00005f000000000000000a0000000000000000000050500000505000000000000000000000500000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f79835 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (81751040 + i)

theorem c79835_0 : rowSum f79835 0 1024 = 25876290 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 79835) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover79835 (by decide)
  decide +kernel

theorem sum79835 : rowSum f79835 0 1024 = 25876290 :=
  c79835_0

theorem h79835 : P.leaf 36 79835 = 25876290 :=
  leaf_weighted (k := 26) (d := 10) (H := 79835) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 79835) (by decide) (by decide +kernel)) sum79835

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

theorem c79839_0 : P.sumLeaves 26 81755136 192 = 9856 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79839) (lo := 0) (len := 192) (W := 9856) check rows elimOK (by decide) (by decide) cover79839 (by decide)
  decide +kernel

theorem contract79839_1 : P.leaf 32 1277427 = 27160 := by
  exact leaf_contract_factors (k := 32) (b := 16) (H := 1277427) (ss := [(22, 1, 433), (2, 1, 482), (3, 1, 531), (4, 1, 580), (5, 1, 629), (6, 1, 636), (7, 1, 825), (17, 1, 874), (18, 8, 1217), (21, 1, 1272), (28, 0, 1315), (30, 0, 1315), (32, 1, 972), (8, 0, 1315), (16, 1, 1210), (9, 1, 1609)]) (ids := [8, 9, 10, 13, 17, 18, 23, 27, 29, 31, 11, 12, 22, 21, 24, 25]) (cs := [1, 1, 1, 1, 1, 1, 0, 1, 2, 3, 4, 12, 13, 5, 1, 1, 0, 6, 7, 1, 1, 15, 14, 8, 16, 17, 0, 9, 0, 10, 1, 11]) (bs := [10, 3, 3]) (W := 27160) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c79839_1 : P.sumLeaves 26 81755328 64 = 27160 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1277427) rows (by decide) (by decide)).symm.trans contract79839_1

theorem c79839_2 : P.sumLeaves 26 81755392 496 = 43356381 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79839) (lo := 256) (len := 496) (W := 43356381) check rows elimOK (by decide) (by decide) cover79839 (by decide)
  decide +kernel

theorem c79839_3 : P.sumLeaves 26 81755888 239 = 112688976 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79839) (lo := 752) (len := 239) (W := 112688976) check rows elimOK (by decide) (by decide) cover79839 (by decide)
  decide +kernel

theorem c79839_4 : P.sumLeaves 26 81756127 33 = 32577256 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79839) (lo := 991) (len := 33) (W := 32577256) check rows elimOK (by decide) (by decide) cover79839 (by decide)
  decide +kernel

theorem h79839 : P.leaf 36 79839 = 188659629 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(192, 9856), (64, 27160), (496, 43356381), (239, 112688976), (33, 32577256)]) (.cons c79839_0 (.cons c79839_1 (.cons c79839_2 (.cons c79839_3 (.cons c79839_4 (.nil)))))) (by decide) (by decide))

theorem cover79852 : P.CoversSplit 26 10 79852 0xfffffffafffffafafffffffafffffafafffcfff8fffcc8c8aaa8aaa8aa888888000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 874, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f79852 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (81768448 + i)

theorem c79852_0 : rowSum f79852 0 983 = 28933056 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 79852) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover79852 (by decide)
  decide +kernel

theorem c79852_1 : rowSum f79852 983 41 = 15713588 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 79852) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover79852 (by decide)
  decide +kernel

theorem sum79852 : rowSum f79852 0 1024 = 44646644 :=
  rowSum_append (F := f79852) (lo := 0) (n := 983) (m := 41) (A := 28933056) (B := 15713588) c79852_0 (c79852_1)

theorem h79852 : P.leaf 36 79852 = 44646644 :=
  leaf_weighted (k := 26) (d := 10) (H := 79852) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 79852) (by decide) (by decide +kernel)) sum79852

theorem cover79853 : P.CoversSplit 26 10 79853 0xfffffffafffffafafffffffafffffafafffcfff8fffcc8c8aaa8aaa8aa8888880000000000000000000000000000000000000000000000000000000000000000fffffffafffffafafffffffafffffafaffccffc8cc00c800aa88aa88880088000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 923, 930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f79853 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (81769472 + i)

theorem c79853_0 : rowSum f79853 0 495 = 25774242 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 79853) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover79853 (by decide)
  decide +kernel

theorem c79853_1 : rowSum f79853 495 479 = 52608382 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 79853) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover79853 (by decide)
  decide +kernel

theorem c79853_2 : rowSum f79853 974 50 = 31142864 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 79853) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover79853 (by decide)
  decide +kernel

theorem sum79853 : rowSum f79853 0 1024 = 109525488 :=
  rowSum_append (F := f79853) (lo := 0) (n := 495) (m := 529) (A := 25774242) (B := 83751246) c79853_0 (rowSum_append (F := f79853) (lo := 495) (n := 479) (m := 50) (A := 52608382) (B := 31142864) c79853_1 (c79853_2))

theorem h79853 : P.leaf 36 79853 = 109525488 :=
  leaf_weighted (k := 26) (d := 10) (H := 79853) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 79853) (by decide) (by decide +kernel)) sum79853

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

theorem cover79855 : P.CoversSplit 26 10 79855 0xfffffffafffffafafffffffafffffafafffcfff8fffcc8c8aaa8aaa8aa8888880000000000000000000000000000000000000000000000000000000000000000fffffffafffffafafffffffafffffafaffccffc8cc00c800aa88aa88880088000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 930, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c79855_0 : P.sumLeaves 26 81771520 440 = 56543194 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79855) (lo := 0) (len := 440) (W := 56543194) check rows elimOK (by decide) (by decide) cover79855 (by decide)
  decide +kernel

theorem c79855_1 : P.sumLeaves 26 81771960 410 = 93620212 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79855) (lo := 440) (len := 410) (W := 93620212) check rows elimOK (by decide) (by decide) cover79855 (by decide)
  decide +kernel

theorem c79855_2 : P.sumLeaves 26 81772370 107 = 128931517 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79855) (lo := 850) (len := 107) (W := 128931517) check rows elimOK (by decide) (by decide) cover79855 (by decide)
  decide +kernel

theorem c79855_3 : P.sumLeaves 26 81772477 67 = 136507112 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79855) (lo := 957) (len := 67) (W := 136507112) check rows elimOK (by decide) (by decide) cover79855 (by decide)
  decide +kernel

theorem h79855 : P.leaf 36 79855 = 415602035 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(440, 56543194), (410, 93620212), (107, 128931517), (67, 136507112)]) (.cons c79855_0 (.cons c79855_1 (.cons c79855_2 (.cons c79855_3 (.nil))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(79835, 360), (79836, 720), (79837, 720), (79838, 720), (79839, 720), (79852, 360), (79853, 360), (79854, 720), (79855, 720)]

theorem segOK : checkSeg 20 perms 79835 79870 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 79835 79870 5400 746353275120 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 746353275120)
    (SegSum.cons (w := 360) h79835 (SegSum.cons (w := 720) h79836 (SegSum.cons (w := 720) h79837 (SegSum.cons (w := 720) h79838 (SegSum.cons (w := 720) h79839 (SegSum.cons (w := 360) h79852 (SegSum.cons (w := 360) h79853 (SegSum.cons (w := 720) h79854 (SegSum.cons (w := 720) h79855 (show SegSum (P.leaf 36) [] 0 from rfl)))))))))) (by decide)

end RACert.S6N0.C0.S51
