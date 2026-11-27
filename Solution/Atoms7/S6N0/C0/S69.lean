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

namespace RACert.S6N0.C0.S69

open RACert RACert.Problem

theorem cover97122 : P.CoversSplit 26 10 97122 0xf000f000f000f0000000000000000000f000f000f000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 874, 972, 979, 1266, 1273, 1658]) (by decide +kernel)

theorem c97122_0 : P.sumLeaves 26 99452928 1024 = 1728000 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97122) (lo := 0) (len := 1024) (W := 1728000) check rows elimOK (by decide) (by decide) cover97122 (by decide)
  decide +kernel

theorem h97122 : P.leaf 36 97122 = 1728000 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1728000)]) (.cons c97122_0 (.nil)) (by decide) (by decide))

theorem cover97123 : P.CoversSplit 26 10 97123 0xf000f000f000f0000000000000000000f000f000f000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 579, 972, 979, 1266, 1273, 1658]) (by decide +kernel)

theorem c97123_0 : P.sumLeaves 26 99453952 1024 = 9401376 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97123) (lo := 0) (len := 1024) (W := 9401376) check rows elimOK (by decide) (by decide) cover97123 (by decide)
  decide +kernel

theorem h97123 : P.leaf 36 97123 = 9401376 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 9401376)]) (.cons c97123_0 (.nil)) (by decide) (by decide))

theorem cover97126 : P.CoversSplit 26 10 97126 0xff00ff00ff00fa000000000000000000ff00ff00ff03fa000500050005000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 874, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97126_0 : P.sumLeaves 26 99457024 1024 = 17000864 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97126) (lo := 0) (len := 1024) (W := 17000864) check rows elimOK (by decide) (by decide) cover97126 (by decide)
  decide +kernel

theorem h97126 : P.leaf 36 97126 = 17000864 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 17000864)]) (.cons c97126_0 (.nil)) (by decide) (by decide))

theorem cover97127 : P.CoversSplit 26 10 97127 0xff00ff00ff00fa000000000000000000ff00ff00ff03fa000500050005000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97127_0 : P.sumLeaves 26 99458048 1024 = 49088144 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97127) (lo := 0) (len := 1024) (W := 49088144) check rows elimOK (by decide) (by decide) cover97127 (by decide)
  decide +kernel

theorem h97127 : P.leaf 36 97127 = 49088144 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 49088144)]) (.cons c97127_0 (.nil)) (by decide) (by decide))

theorem cover97130 : P.CoversSplit 26 10 97130 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0c000000005000000000000000000000000000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f00000000000000005000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 874, 972, 979, 1266, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c97130_0 : P.sumLeaves 26 99461120 990 = 7574464 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97130) (lo := 0) (len := 990) (W := 7574464) check rows elimOK (by decide) (by decide) cover97130 (by decide)
  decide +kernel

theorem c97130_1 : P.sumLeaves 26 99462110 34 = 6790400 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97130) (lo := 990) (len := 34) (W := 6790400) check rows elimOK (by decide) (by decide) cover97130 (by decide)
  decide +kernel

theorem h97130 : P.leaf 36 97130 = 14364864 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(990, 7574464), (34, 6790400)]) (.cons c97130_0 (.cons c97130_1 (.nil))) (by decide) (by decide))

theorem cover97131 : P.CoversSplit 26 10 97131 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0c000000005000000000000000000000000000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f00000000000000005000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 579, 972, 979, 1266, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c97131_0 : P.sumLeaves 26 99462144 990 = 23496796 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97131) (lo := 0) (len := 990) (W := 23496796) check rows elimOK (by decide) (by decide) cover97131 (by decide)
  decide +kernel

theorem c97131_1 : P.sumLeaves 26 99463134 34 = 13018944 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97131) (lo := 990) (len := 34) (W := 13018944) check rows elimOK (by decide) (by decide) cover97131 (by decide)
  decide +kernel

theorem h97131 : P.leaf 36 97131 = 36515740 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(990, 23496796), (34, 13018944)]) (.cons c97131_0 (.cons c97131_1 (.nil))) (by decide) (by decide))

theorem cover97133 : P.CoversSplit 26 10 97133 0xfffffffffffffafa0000000000000000fffffffffffcfac805050500050000000000000000000000000000000000000000000000000000000000000000000000fffffffffffffafa0000000000000000ffffffff0000000005050500000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 923, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97133_0 : P.sumLeaves 26 99464192 510 = 4832832 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97133) (lo := 0) (len := 510) (W := 4832832) check rows elimOK (by decide) (by decide) cover97133 (by decide)
  decide +kernel

theorem c97133_1 : P.sumLeaves 26 99464702 485 = 11277704 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97133) (lo := 510) (len := 485) (W := 11277704) check rows elimOK (by decide) (by decide) cover97133 (by decide)
  decide +kernel

theorem c97133_2 : P.sumLeaves 26 99465187 29 = 8789344 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97133) (lo := 995) (len := 29) (W := 8789344) check rows elimOK (by decide) (by decide) cover97133 (by decide)
  decide +kernel

theorem h97133 : P.leaf 36 97133 = 24899880 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(510, 4832832), (485, 11277704), (29, 8789344)]) (.cons c97133_0 (.cons c97133_1 (.cons c97133_2 (.nil)))) (by decide) (by decide))

theorem cover97134 : P.CoversSplit 26 10 97134 0xfffffffffffffafa0000000000000000fffffffffffcfac805050500050000000000000000000000000000000000000000000000000000000000000000000000fffffffffffffafa0000000000000000ffffffff0000000005050500000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 874, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97134_0 : P.sumLeaves 26 99465216 510 = 6238064 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97134) (lo := 0) (len := 510) (W := 6238064) check rows elimOK (by decide) (by decide) cover97134 (by decide)
  decide +kernel

theorem c97134_1 : P.sumLeaves 26 99465726 485 = 21181032 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97134) (lo := 510) (len := 485) (W := 21181032) check rows elimOK (by decide) (by decide) cover97134 (by decide)
  decide +kernel

theorem c97134_2 : P.sumLeaves 26 99466211 29 = 14086880 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97134) (lo := 995) (len := 29) (W := 14086880) check rows elimOK (by decide) (by decide) cover97134 (by decide)
  decide +kernel

theorem h97134 : P.leaf 36 97134 = 41505976 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(510, 6238064), (485, 21181032), (29, 14086880)]) (.cons c97134_0 (.cons c97134_1 (.cons c97134_2 (.nil)))) (by decide) (by decide))

theorem cover97135 : P.CoversSplit 26 10 97135 0xfffffffffffffafa0000000000000000fffffffffffcfac805050500050000000000000000000000000000000000000000000000000000000000000000000000fffffffffffffafa0000000000000000ffffffff0000000005050500000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97135_0 : P.sumLeaves 26 99466240 510 = 16551072 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97135) (lo := 0) (len := 510) (W := 16551072) check rows elimOK (by decide) (by decide) cover97135 (by decide)
  decide +kernel

theorem c97135_1 : P.sumLeaves 26 99466750 485 = 60384104 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97135) (lo := 510) (len := 485) (W := 60384104) check rows elimOK (by decide) (by decide) cover97135 (by decide)
  decide +kernel

theorem c97135_2 : P.sumLeaves 26 99467235 29 = 24148640 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97135) (lo := 995) (len := 29) (W := 24148640) check rows elimOK (by decide) (by decide) cover97135 (by decide)
  decide +kernel

theorem h97135 : P.leaf 36 97135 = 101083816 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(510, 16551072), (485, 60384104), (29, 24148640)]) (.cons c97135_0 (.cons c97135_1 (.cons c97135_2 (.nil)))) (by decide) (by decide))

theorem cover97139 : P.CoversSplit 26 10 97139 0xf000f000f000f0000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 972, 979, 1273, 1658, 1665]) (by decide +kernel)

theorem c97139_0 : P.sumLeaves 26 99470336 1024 = 67601920 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97139) (lo := 0) (len := 1024) (W := 67601920) check rows elimOK (by decide) (by decide) cover97139 (by decide)
  decide +kernel

theorem h97139 : P.leaf 36 97139 = 67601920 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 67601920)]) (.cons c97139_0 (.nil)) (by decide) (by decide))

theorem cover97140 : P.CoversSplit 26 10 97140 0xff00ff00ff00fa000000000000000000ff00ff00ff03fa000500050005000000050000000500000005000000050000000500000005010000050000000500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 874, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97140_0 : P.sumLeaves 26 99471360 1024 = 15588698 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97140) (lo := 0) (len := 1024) (W := 15588698) check rows elimOK (by decide) (by decide) cover97140 (by decide)
  decide +kernel

theorem h97140 : P.leaf 36 97140 = 15588698 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 15588698)]) (.cons c97140_0 (.nil)) (by decide) (by decide))

theorem cover97141 : P.CoversSplit 26 10 97141 0xff00ff00ff00fa000000000000000000ff00ff00ff03fa000500050005000000050000000500000005000000050000000500000005010000050000000500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 923, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97141_0 : P.sumLeaves 26 99472384 1024 = 165011375 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97141) (lo := 0) (len := 1024) (W := 165011375) check rows elimOK (by decide) (by decide) cover97141 (by decide)
  decide +kernel

theorem h97141 : P.leaf 36 97141 = 165011375 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 165011375)]) (.cons c97141_0 (.nil)) (by decide) (by decide))

theorem cover97142 : P.CoversSplit 26 10 97142 0xff00ff00ff00fa000000000000000000ff00ff00ff03fa000500050005000000050000000500000005000000050000000500000005010000050000000500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 874, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97142_0 : P.sumLeaves 26 99473408 1024 = 172035492 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97142) (lo := 0) (len := 1024) (W := 172035492) check rows elimOK (by decide) (by decide) cover97142 (by decide)
  decide +kernel

theorem h97142 : P.leaf 36 97142 = 172035492 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 172035492)]) (.cons c97142_0 (.nil)) (by decide) (by decide))

theorem cover97143 : P.CoversSplit 26 10 97143 0xff00ff00ff00fa000000000000000000ff00ff00ff03fa000500050005000000050000000500000005000000050000000500000005010000050000000500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97143_0 : P.sumLeaves 26 99474432 1024 = 377872115 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97143) (lo := 0) (len := 1024) (W := 377872115) check rows elimOK (by decide) (by decide) cover97143 (by decide)
  decide +kernel

theorem h97143 : P.leaf 36 97143 = 377872115 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 377872115)]) (.cons c97143_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(97122, 240), (97123, 720), (97126, 720), (97127, 720), (97130, 720), (97131, 720), (97133, 720), (97134, 720), (97135, 720), (97139, 720), (97140, 360), (97141, 720), (97142, 720), (97143, 720)]

theorem segOK : checkSeg 20 perms 97122 97145 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 97122 97145 9240 781021375920 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 781021375920)
    (SegSum.cons (w := 240) h97122 (SegSum.cons (w := 720) h97123 (SegSum.cons (w := 720) h97126 (SegSum.cons (w := 720) h97127 (SegSum.cons (w := 720) h97130 (SegSum.cons (w := 720) h97131 (SegSum.cons (w := 720) h97133 (SegSum.cons (w := 720) h97134 (SegSum.cons (w := 720) h97135 (SegSum.cons (w := 720) h97139 (SegSum.cons (w := 360) h97140 (SegSum.cons (w := 720) h97141 (SegSum.cons (w := 720) h97142 (SegSum.cons (w := 720) h97143 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))) (by decide)

end RACert.S6N0.C0.S69
