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

namespace RACert.S6N0.C0.S45

open RACert RACert.Problem

theorem cover78814 : P.CoversSplit 26 10 78814 0xffff0000ffff0500ffff0000ffff050000000000000000000000000000000000050500000505000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 867, 873, 880, 972, 1315, 1658]) (by decide +kernel)

theorem c78814_0 : P.sumLeaves 26 80705536 1024 = 3299858 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78814) (lo := 0) (len := 1024) (W := 3299858) check rows elimOK (by decide) (by decide) cover78814 (by decide)
  decide +kernel

theorem h78814 : P.leaf 36 78814 = 3299858 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3299858)]) (.cons c78814_0 (.nil)) (by decide) (by decide))

theorem cover78815 : P.CoversSplit 26 10 78815 0xffff0000ffff0500ffff0000ffff0500fffc0000fffc0000aaa80000aa8800000505000005050000000000000000000005040000050400000000000000000000ffff0000ffff0500ffff0000ffff0500ffcc000000000000aa880000000000000505000005050000000000000000000005040000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 873, 930, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c78815_0 : P.sumLeaves 26 80706560 192 = 4032 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78815) (lo := 0) (len := 192) (W := 4032) check rows elimOK (by decide) (by decide) cover78815 (by decide)
  decide +kernel

theorem contract78815_1 : P.leaf 32 1261043 = 10584 := by
  exact leaf_contract_factors (k := 32) (b := 15) (H := 1261043) (ss := [(22, 1, 433), (2, 1, 482), (3, 1, 531), (4, 1, 580), (5, 1, 629), (6, 1, 636), (7, 1, 825), (17, 1, 874), (18, 8, 1217), (21, 1, 1272), (28, 0, 1315), (30, 0, 1315), (14, 1, 873), (32, 1, 873), (8, 0, 1315), (16, 1, 1210), (9, 1, 1609)]) (ids := [8, 9, 10, 13, 17, 18, 23, 24, 25, 27, 29, 31, 11, 22, 21]) (cs := [1, 1, 1, 1, 1, 1, 0, 1, 2, 3, 4, 14, 1, 5, 1, 1, 0, 6, 7, 1, 1, 16, 15, 8, 9, 10, 0, 11, 0, 12, 1, 13]) (bs := [12, 2, 1]) (W := 10584) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c78815_1 : P.sumLeaves 26 80706752 64 = 10584 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1261043) rows (by decide) (by decide)).symm.trans contract78815_1

theorem c78815_2 : P.sumLeaves 26 80706816 496 = 18288089 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78815) (lo := 256) (len := 496) (W := 18288089) check rows elimOK (by decide) (by decide) cover78815 (by decide)
  decide +kernel

theorem c78815_3 : P.sumLeaves 26 80707312 239 = 42769127 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78815) (lo := 752) (len := 239) (W := 42769127) check rows elimOK (by decide) (by decide) cover78815 (by decide)
  decide +kernel

theorem c78815_4 : P.sumLeaves 26 80707551 33 = 13617103 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78815) (lo := 991) (len := 33) (W := 13617103) check rows elimOK (by decide) (by decide) cover78815 (by decide)
  decide +kernel

theorem h78815 : P.leaf 36 78815 = 74688935 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(192, 4032), (64, 10584), (496, 18288089), (239, 42769127), (33, 13617103)]) (.cons c78815_0 (.cons c78815_1 (.cons c78815_2 (.cons c78815_3 (.cons c78815_4 (.nil)))))) (by decide) (by decide))

theorem cover78846 : P.CoversSplit 26 10 78846 0xfffffffafffffafafffffffafffffafa00000000000000000000000000000000fffff0f0fffff0f0aaaaa0a0aaaaa0a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [867, 873, 874, 972, 1315, 1658]) (by decide +kernel)

noncomputable def f78846 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (80738304 + i)

theorem c78846_0 : rowSum f78846 0 986 = 19012040 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 78846) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover78846 (by decide)
  decide +kernel

theorem c78846_1 : rowSum f78846 986 38 = 7888102 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 78846) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover78846 (by decide)
  decide +kernel

theorem sum78846 : rowSum f78846 0 1024 = 26900142 :=
  rowSum_append (F := f78846) (lo := 0) (n := 986) (m := 38) (A := 19012040) (B := 7888102) c78846_0 (c78846_1)

theorem h78846 : P.leaf 36 78846 = 26900142 :=
  leaf_weighted (k := 26) (d := 10) (H := 78846) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 78846) (by decide) (by decide +kernel)) sum78846

theorem cover78847 : P.CoversSplit 26 10 78847 0xfffffffafffffafafffffffafffffafafffcfff8fffcc8c8aaa8aaa8aa888888fffffafafffffafaaaaaaaaaaaaaaaaafffcfaf8fffcc8c8aaa8aaa8aa888888fffffffafffffafafffffffafffffafaffccffc8ccccc8c8aa88aa8888888888fffffafafffffafaaaaaaaaaaaaaaaaaffccfac8ccccc8c8aa88aa8888888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 930, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f78847 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (80739328 + i)

theorem c78847_0 : rowSum f78847 0 297 = 44779412 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 78847) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover78847 (by decide)
  decide +kernel

theorem c78847_1 : rowSum f78847 297 197 = 436574784 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 78847) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover78847 (by decide)
  decide +kernel

theorem c78847_2 : rowSum f78847 494 255 = 546348410 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 78847) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover78847 (by decide)
  decide +kernel

theorem c78847_3 : rowSum f78847 749 223 = 702835225 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 78847) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover78847 (by decide)
  decide +kernel

theorem c78847_4 : rowSum f78847 972 52 = 324610405 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 78847) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover78847 (by decide)
  decide +kernel

theorem sum78847 : rowSum f78847 0 1024 = 2055148236 :=
  rowSum_append (F := f78847) (lo := 0) (n := 297) (m := 727) (A := 44779412) (B := 2010368824) c78847_0 (rowSum_append (F := f78847) (lo := 297) (n := 197) (m := 530) (A := 436574784) (B := 1573794040) c78847_1 (rowSum_append (F := f78847) (lo := 494) (n := 255) (m := 275) (A := 546348410) (B := 1027445630) c78847_2 (rowSum_append (F := f78847) (lo := 749) (n := 223) (m := 52) (A := 702835225) (B := 324610405) c78847_3 (c78847_4))))

theorem h78847 : P.leaf 36 78847 = 2055148236 :=
  leaf_weighted (k := 26) (d := 10) (H := 78847) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 78847) (by decide) (by decide +kernel)) sum78847

theorem h79068 : P.leaf 36 79068 = 123904 := by
  exact leaf_contract_factors (k := 36) (b := 19) (H := 79068) (ss := [(32, 1, 467), (35, 1, 475), (37, 17, 531), (17, 1, 537), (36, 1, 580), (21, 1, 586), (29, 1, 587), (9, 1, 573), (28, 1, 629), (15, 1, 916), (31, 1, 930), (30, 1, 972), (18, 1, 1217), (19, 1, 1259), (33, 1, 1273), (20, 1, 1609), (34, 1, 1658)]) (ids := [0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 14, 20, 21, 22, 23, 24, 25]) (cs := [2, 3, 4, 5, 6, 7, 8, 1, 9, 10, 11, 12, 13, 1, 14, 1, 1, 1, 1, 1, 15, 16, 17, 18, 19, 20, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [15, 4]) (W := 123904) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem h79069 : P.leaf 36 79069 = 123904 := by
  exact leaf_contract_factors (k := 36) (b := 19) (H := 79069) (ss := [(35, 1, 475), (37, 17, 531), (17, 1, 537), (36, 1, 580), (21, 1, 586), (29, 1, 587), (9, 1, 573), (28, 1, 629), (15, 1, 916), (31, 1, 930), (30, 1, 972), (18, 1, 1217), (19, 1, 1259), (33, 1, 1273), (32, 1, 1315), (20, 1, 1609), (34, 1, 1658)]) (ids := [0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 14, 20, 21, 22, 23, 24, 25]) (cs := [2, 3, 4, 5, 6, 7, 8, 1, 9, 10, 11, 12, 13, 1, 14, 1, 1, 1, 1, 1, 15, 16, 17, 18, 19, 20, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [15, 4]) (W := 123904) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem h79070 : P.leaf 36 79070 = 123904 := by
  exact leaf_contract_factors (k := 36) (b := 19) (H := 79070) (ss := [(37, 17, 531), (17, 1, 537), (36, 1, 580), (21, 1, 586), (29, 1, 587), (9, 1, 573), (35, 1, 587), (28, 1, 629), (15, 1, 916), (31, 1, 930), (30, 1, 972), (18, 1, 1217), (19, 1, 1259), (33, 1, 1273), (32, 1, 1315), (20, 1, 1609), (34, 1, 1658)]) (ids := [0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 14, 20, 21, 22, 23, 24, 25]) (cs := [2, 3, 4, 5, 6, 7, 8, 1, 9, 10, 11, 12, 13, 1, 14, 1, 1, 1, 1, 1, 15, 16, 17, 18, 19, 20, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [15, 4]) (W := 123904) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem h79071 : P.leaf 36 79071 = 123904 := by
  exact leaf_contract_factors (k := 36) (b := 19) (H := 79071) (ss := [(37, 17, 531), (17, 1, 537), (36, 1, 580), (21, 1, 586), (29, 1, 587), (9, 1, 573), (35, 1, 587), (28, 1, 629), (15, 1, 916), (31, 1, 930), (30, 1, 972), (18, 1, 1217), (19, 1, 1259), (33, 1, 1273), (32, 1, 1315), (20, 1, 1609), (34, 1, 1658)]) (ids := [0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 14, 20, 21, 22, 23, 24, 25]) (cs := [2, 3, 4, 5, 6, 7, 8, 1, 9, 10, 11, 12, 13, 1, 14, 1, 1, 1, 1, 1, 15, 16, 17, 18, 19, 20, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [15, 4]) (W := 123904) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem h79086 : P.leaf 36 79086 = 245216 := by
  exact leaf_contract_factors (k := 36) (b := 21) (H := 79086) (ss := [(35, 1, 524), (36, 1, 580), (21, 1, 586), (29, 1, 636), (9, 1, 573), (28, 1, 629), (37, 1, 636), (15, 1, 916), (31, 1, 930), (30, 1, 972), (19, 1, 1259), (33, 1, 1273), (32, 1, 1315), (20, 1, 1609), (34, 1, 1658)]) (ids := [0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 14, 15, 16, 20, 21, 22, 23, 24, 25]) (cs := [2, 3, 4, 5, 6, 7, 8, 1, 9, 10, 11, 12, 13, 1, 14, 15, 16, 1, 1, 1, 17, 18, 19, 20, 21, 22, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [18, 3]) (W := 245216) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem h79087 : P.leaf 36 79087 = 245216 := by
  exact leaf_contract_factors (k := 36) (b := 21) (H := 79087) (ss := [(35, 1, 524), (36, 1, 580), (21, 1, 586), (29, 1, 636), (9, 1, 573), (28, 1, 629), (37, 1, 636), (15, 1, 916), (31, 1, 930), (30, 1, 972), (19, 1, 1259), (33, 1, 1273), (32, 1, 1315), (20, 1, 1609), (34, 1, 1658)]) (ids := [0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 14, 15, 16, 20, 21, 22, 23, 24, 25]) (cs := [2, 3, 4, 5, 6, 7, 8, 1, 9, 10, 11, 12, 13, 1, 14, 15, 16, 1, 1, 1, 17, 18, 19, 20, 21, 22, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [18, 3]) (W := 245216) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem h79102 : P.leaf 36 79102 = 306152 := by
  exact leaf_contract_factors (k := 36) (b := 21) (H := 79102) (ss := [(36, 1, 580), (21, 1, 586), (37, 1, 874), (29, 1, 587), (9, 1, 573), (35, 1, 587), (28, 1, 629), (15, 1, 916), (31, 1, 930), (30, 1, 972), (19, 1, 1259), (33, 1, 1273), (32, 1, 1315), (20, 1, 1609), (34, 1, 1658)]) (ids := [0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 14, 15, 16, 20, 21, 22, 23, 24, 25]) (cs := [2, 3, 4, 5, 6, 7, 8, 1, 9, 10, 11, 12, 13, 1, 14, 15, 16, 1, 1, 1, 17, 18, 19, 20, 21, 22, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [18, 3]) (W := 306152) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem h79103 : P.leaf 36 79103 = 306152 := by
  exact leaf_contract_factors (k := 36) (b := 21) (H := 79103) (ss := [(36, 1, 580), (21, 1, 586), (37, 1, 874), (29, 1, 587), (9, 1, 573), (35, 1, 587), (28, 1, 629), (15, 1, 916), (31, 1, 930), (30, 1, 972), (19, 1, 1259), (33, 1, 1273), (32, 1, 1315), (20, 1, 1609), (34, 1, 1658)]) (ids := [0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 14, 15, 16, 20, 21, 22, 23, 24, 25]) (cs := [2, 3, 4, 5, 6, 7, 8, 1, 9, 10, 11, 12, 13, 1, 14, 15, 16, 1, 1, 1, 17, 18, 19, 20, 21, 22, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [18, 3]) (W := 306152) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover79159 : P.CoversSplit 26 10 79159 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000200000000001000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [482, 489, 538, 629, 636, 930, 972, 1315, 1658]) (by decide +kernel)

noncomputable def f79159 (i : ℕ) := rowWeight keep9 twice9 i * P.leaf 26 (81058816 + i)

theorem c79159_0 : rowSum f79159 0 1024 = 280129 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 79159) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover79159 (by decide)
  decide +kernel

theorem sum79159 : rowSum f79159 0 1024 = 280129 :=
  c79159_0

theorem h79159 : P.leaf 36 79159 = 280129 :=
  leaf_weighted (k := 26) (d := 10) (H := 79159) (keep := keep9) (twice := twice9) rows (by decide) (by decide) bal9 (invRow9 (H := 79159) (by decide) (by decide +kernel)) sum79159

theorem h79163 : P.leaf 36 79163 = 245760 := by
  exact leaf_contract_factors (k := 36) (b := 18) (H := 79163) (ss := [(37, 1, 482), (36, 1, 531), (28, 1, 481), (30, 1, 481), (18, 1, 537), (5, 1, 586), (6, 1, 433), (29, 1, 636), (12, 1, 880), (13, 1, 825), (21, 1, 929), (31, 1, 979), (17, 1, 1217), (33, 1, 1273), (35, 1, 1273), (32, 1, 1315), (20, 1, 1609), (34, 1, 1658)]) (ids := [0, 5, 14, 17, 1, 2, 6, 7, 8, 9, 12, 13, 20, 21, 22, 23, 24, 25]) (cs := [2, 6, 7, 1, 1, 3, 8, 9, 10, 11, 1, 1, 12, 13, 4, 1, 1, 5, 1, 1, 14, 15, 16, 17, 18, 19, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [4, 14]) (W := 245760) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover79164 : P.CoversSplit 26 10 79164 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 580, 629, 636, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c79164_0 : P.sumLeaves 26 81063936 1024 = 81508 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79164) (lo := 0) (len := 1024) (W := 81508) check rows elimOK (by decide) (by decide) cover79164 (by decide)
  decide +kernel

theorem h79164 : P.leaf 36 79164 = 81508 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 81508)]) (.cons c79164_0 (.nil)) (by decide) (by decide))

theorem cover79165 : P.CoversSplit 26 10 79165 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 580, 629, 636, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c79165_0 : P.sumLeaves 26 81064960 1024 = 238852 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79165) (lo := 0) (len := 1024) (W := 238852) check rows elimOK (by decide) (by decide) cover79165 (by decide)
  decide +kernel

theorem h79165 : P.leaf 36 79165 = 238852 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 238852)]) (.cons c79165_0 (.nil)) (by decide) (by decide))

theorem cover79167 : P.CoversSplit 26 10 79167 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 580, 629, 636, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c79167_0 : P.sumLeaves 26 81067008 1024 = 770884 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79167) (lo := 0) (len := 1024) (W := 770884) check rows elimOK (by decide) (by decide) cover79167 (by decide)
  decide +kernel

theorem h79167 : P.leaf 36 79167 = 770884 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 770884)]) (.cons c79167_0 (.nil)) (by decide) (by decide))

theorem h79196 : P.leaf 36 79196 = 81920 := by
  exact leaf_contract_factors (k := 36) (b := 17) (H := 79196) (ss := [(32, 10, 467), (10, 1, 479), (37, 1, 531), (5, 1, 586), (3, 1, 418), (4, 1, 425), (28, 1, 629), (36, 1, 629), (29, 1, 636), (17, 1, 874), (30, 1, 972), (31, 1, 979), (18, 1, 1217), (21, 1, 1272), (15, 1, 916), (33, 1, 1322), (20, 1, 1609), (34, 1, 1658), (35, 1, 1665)]) (ids := [5, 6, 9, 10, 11, 14, 17, 21, 0, 4, 7, 12, 20, 22, 23, 24, 25]) (cs := [10, 1, 1, 1, 11, 2, 3, 12, 1, 4, 5, 6, 13, 1, 7, 1, 1, 8, 1, 1, 14, 9, 15, 16, 17, 18, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [8, 9]) (W := 81920) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem h79197 : P.leaf 36 79197 = 260608 := by
  exact leaf_contract_factors (k := 36) (b := 19) (H := 79197) (ss := [(37, 1, 531), (5, 1, 586), (17, 1, 874), (36, 1, 923), (28, 1, 530), (32, 1, 530), (29, 1, 636), (30, 1, 972), (31, 1, 979), (18, 1, 1217), (21, 1, 1272), (15, 1, 916), (33, 1, 1322), (20, 1, 1609), (34, 1, 1658), (4, 1, 425), (35, 1, 1665)]) (ids := [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 14, 17, 20, 21, 12, 22, 23, 24, 25]) (cs := [2, 3, 1, 1, 4, 5, 6, 7, 8, 9, 10, 11, 16, 1, 12, 1, 1, 13, 1, 1, 14, 15, 17, 18, 19, 20, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [14, 5]) (W := 260608) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem h79198 : P.leaf 36 79198 = 231552 := by
  exact leaf_contract_factors (k := 36) (b := 19) (H := 79198) (ss := [(10, 1, 467), (37, 1, 531), (5, 1, 586), (17, 1, 874), (36, 1, 923), (28, 1, 530), (32, 1, 530), (3, 1, 418), (29, 1, 636), (30, 1, 972), (31, 1, 979), (18, 1, 1217), (21, 1, 1272), (33, 1, 1322), (20, 1, 1609), (34, 1, 1658), (35, 1, 1665)]) (ids := [0, 2, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14, 17, 20, 21, 22, 23, 24, 25]) (cs := [2, 1, 3, 1, 4, 5, 6, 7, 1, 8, 9, 10, 11, 12, 13, 1, 1, 14, 1, 1, 15, 16, 17, 18, 19, 20, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [15, 4]) (W := 231552) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem h79199 : P.leaf 36 79199 = 853504 := by
  exact leaf_contract_factors (k := 36) (b := 21) (H := 79199) (ss := [(37, 1, 531), (5, 1, 586), (17, 1, 874), (36, 1, 923), (28, 1, 530), (32, 1, 530), (29, 1, 636), (30, 1, 972), (31, 1, 979), (18, 1, 1217), (21, 1, 1272), (33, 1, 1322), (20, 1, 1609), (34, 1, 1658), (35, 1, 1665)]) (ids := [0, 1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 17, 20, 21, 22, 23, 24, 25]) (cs := [2, 3, 4, 1, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 1, 1, 16, 1, 1, 17, 18, 19, 20, 21, 22, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [17, 4]) (W := 853504) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover79212 : P.CoversSplit 26 10 79212 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 873, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c79212_0 : P.sumLeaves 26 81113088 1024 = 124056 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79212) (lo := 0) (len := 1024) (W := 124056) check rows elimOK (by decide) (by decide) cover79212 (by decide)
  decide +kernel

theorem h79212 : P.leaf 36 79212 = 124056 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 124056)]) (.cons c79212_0 (.nil)) (by decide) (by decide))

theorem cover79213 : P.CoversSplit 26 10 79213 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c79213_0 : P.sumLeaves 26 81114112 1024 = 153132 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79213) (lo := 0) (len := 1024) (W := 153132) check rows elimOK (by decide) (by decide) cover79213 (by decide)
  decide +kernel

theorem h79213 : P.leaf 36 79213 = 153132 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 153132)]) (.cons c79213_0 (.nil)) (by decide) (by decide))

theorem cover79214 : P.CoversSplit 26 10 79214 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 873, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c79214_0 : P.sumLeaves 26 81115136 1024 = 559542 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79214) (lo := 0) (len := 1024) (W := 559542) check rows elimOK (by decide) (by decide) cover79214 (by decide)
  decide +kernel

theorem h79214 : P.leaf 36 79214 = 559542 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 559542)]) (.cons c79214_0 (.nil)) (by decide) (by decide))

theorem cover79215 : P.CoversSplit 26 10 79215 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c79215_0 : P.sumLeaves 26 81116160 1024 = 775504 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79215) (lo := 0) (len := 1024) (W := 775504) check rows elimOK (by decide) (by decide) cover79215 (by decide)
  decide +kernel

theorem h79215 : P.leaf 36 79215 = 775504 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 775504)]) (.cons c79215_0 (.nil)) (by decide) (by decide))

theorem cover79230 : P.CoversSplit 26 10 79230 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 873, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c79230_0 : P.sumLeaves 26 81131520 1024 = 1942709 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79230) (lo := 0) (len := 1024) (W := 1942709) check rows elimOK (by decide) (by decide) cover79230 (by decide)
  decide +kernel

theorem h79230 : P.leaf 36 79230 = 1942709 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1942709)]) (.cons c79230_0 (.nil)) (by decide) (by decide))

theorem cover79231 : P.CoversSplit 26 10 79231 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c79231_0 : P.sumLeaves 26 81132544 1024 = 2958212 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79231) (lo := 0) (len := 1024) (W := 2958212) check rows elimOK (by decide) (by decide) cover79231 (by decide)
  decide +kernel

theorem h79231 : P.leaf 36 79231 = 2958212 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2958212)]) (.cons c79231_0 (.nil)) (by decide) (by decide))

theorem cover79269 : P.CoversSplit 26 10 79269 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000200000000001000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 538, 629, 636, 930, 972, 979, 1315, 1658]) (by decide +kernel)

theorem c79269_0 : P.sumLeaves 26 81171456 1024 = 68444 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79269) (lo := 0) (len := 1024) (W := 68444) check rows elimOK (by decide) (by decide) cover79269 (by decide)
  decide +kernel

theorem h79269 : P.leaf 36 79269 = 68444 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 68444)]) (.cons c79269_0 (.nil)) (by decide) (by decide))

theorem cover79271 : P.CoversSplit 26 10 79271 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000200000000001000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 538, 629, 636, 930, 972, 1315, 1658]) (by decide +kernel)

theorem c79271_0 : P.sumLeaves 26 81173504 1024 = 231996 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79271) (lo := 0) (len := 1024) (W := 231996) check rows elimOK (by decide) (by decide) cover79271 (by decide)
  decide +kernel

theorem h79271 : P.leaf 36 79271 = 231996 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 231996)]) (.cons c79271_0 (.nil)) (by decide) (by decide))

theorem cover79276 : P.CoversSplit 26 10 79276 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 566, 629, 636, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c79276_0 : P.sumLeaves 26 81178624 1024 = 39664 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79276) (lo := 0) (len := 1024) (W := 39664) check rows elimOK (by decide) (by decide) cover79276 (by decide)
  decide +kernel

theorem h79276 : P.leaf 36 79276 = 39664 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 39664)]) (.cons c79276_0 (.nil)) (by decide) (by decide))

theorem cover79277 : P.CoversSplit 26 10 79277 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 566, 629, 636, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c79277_0 : P.sumLeaves 26 81179648 1024 = 249636 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79277) (lo := 0) (len := 1024) (W := 249636) check rows elimOK (by decide) (by decide) cover79277 (by decide)
  decide +kernel

theorem h79277 : P.leaf 36 79277 = 249636 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 249636)]) (.cons c79277_0 (.nil)) (by decide) (by decide))

theorem cover79278 : P.CoversSplit 26 10 79278 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 629, 636, 874, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c79278_0 : P.sumLeaves 26 81180672 1024 = 75048 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79278) (lo := 0) (len := 1024) (W := 75048) check rows elimOK (by decide) (by decide) cover79278 (by decide)
  decide +kernel

theorem h79278 : P.leaf 36 79278 = 75048 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 75048)]) (.cons c79278_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(78814, 720), (78815, 720), (78846, 180), (78847, 180), (79068, 360), (79069, 360), (79070, 360), (79071, 360), (79086, 360), (79087, 360), (79102, 360), (79103, 360), (79159, 90), (79163, 180), (79164, 360), (79165, 720), (79167, 360), (79196, 720), (79197, 720), (79198, 720), (79199, 720), (79212, 360), (79213, 360), (79214, 720), (79215, 720), (79230, 360), (79231, 360), (79269, 180), (79271, 360), (79276, 720), (79277, 720), (79278, 720)]

theorem segOK : checkSeg 20 perms 78814 79279 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 78814 79279 14850 436255710570 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 436255710570)
    (SegSum.cons (w := 720) h78814 (SegSum.cons (w := 720) h78815 (SegSum.cons (w := 180) h78846 (SegSum.cons (w := 180) h78847 (SegSum.cons (w := 360) h79068 (SegSum.cons (w := 360) h79069 (SegSum.cons (w := 360) h79070 (SegSum.cons (w := 360) h79071 (SegSum.cons (w := 360) h79086 (SegSum.cons (w := 360) h79087 (SegSum.cons (w := 360) h79102 (SegSum.cons (w := 360) h79103 (SegSum.cons (w := 90) h79159 (SegSum.cons (w := 180) h79163 (SegSum.cons (w := 360) h79164 (SegSum.cons (w := 720) h79165 (SegSum.cons (w := 360) h79167 (SegSum.cons (w := 720) h79196 (SegSum.cons (w := 720) h79197 (SegSum.cons (w := 720) h79198 (SegSum.cons (w := 720) h79199 (SegSum.cons (w := 360) h79212 (SegSum.cons (w := 360) h79213 (SegSum.cons (w := 720) h79214 (SegSum.cons (w := 720) h79215 (SegSum.cons (w := 360) h79230 (SegSum.cons (w := 360) h79231 (SegSum.cons (w := 180) h79269 (SegSum.cons (w := 360) h79271 (SegSum.cons (w := 720) h79276 (SegSum.cons (w := 720) h79277 (SegSum.cons (w := 720) h79278 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S45
