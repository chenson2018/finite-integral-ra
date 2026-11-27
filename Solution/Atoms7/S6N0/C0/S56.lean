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

namespace RACert.S6N0.C0.S56

open RACert RACert.Problem

theorem cover81886 : P.CoversSplit 26 10 81886 0xffff0000ffff0500ffff0000ffff0500ffff0000fffc0500aaaa0000aa8800000505000005050000000000000000000005050000050400000000000000000000ffff0000ffff0500ffff0000ffff0500ffff0000ff000500aaaa0000aa0000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 880, 930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c81886_0 : P.sumLeaves 26 83851264 502 = 64903808 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81886) (lo := 0) (len := 502) (W := 64903808) check rows elimOK (by decide) (by decide) cover81886 (by decide)
  decide +kernel

theorem c81886_1 : P.sumLeaves 26 83851766 449 = 145368604 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81886) (lo := 502) (len := 449) (W := 145368604) check rows elimOK (by decide) (by decide) cover81886 (by decide)
  decide +kernel

theorem c81886_2 : P.sumLeaves 26 83852215 73 = 147288364 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81886) (lo := 951) (len := 73) (W := 147288364) check rows elimOK (by decide) (by decide) cover81886 (by decide)
  decide +kernel

theorem h81886 : P.leaf 36 81886 = 357560776 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(502, 64903808), (449, 145368604), (73, 147288364)]) (.cons c81886_0 (.cons c81886_1 (.cons c81886_2 (.nil)))) (by decide) (by decide))

theorem cover81887 : P.CoversSplit 26 10 81887 0xffff0000ffff0500ffff0000ffff0500ffff0000fffc0500aaaa0000aa8800000505000005050000000000000000000005050000050400000000000000000000ffff0000ffff0500ffff0000ffff0500ffff0000ff000500aaaa0000aa0000000505000005050000000000000000000005050000050000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c81887_0 : P.sumLeaves 26 83852288 192 = 74294 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81887) (lo := 0) (len := 192) (W := 74294) check rows elimOK (by decide) (by decide) cover81887 (by decide)
  decide +kernel

theorem contract81887_1 : P.leaf 32 1310195 = 124000 := by
  exact leaf_contract_factors (k := 32) (b := 18) (H := 1310195) (ss := [(22, 1, 433), (2, 1, 482), (3, 1, 531), (4, 1, 580), (5, 1, 629), (6, 1, 636), (7, 1, 825), (8, 1, 1217), (21, 1, 1272), (28, 0, 1315), (30, 0, 1315), (32, 1, 972), (18, 0, 1315), (9, 1, 1609)]) (ids := [8, 9, 10, 11, 13, 14, 15, 17, 18, 21, 23, 24, 27, 29, 31, 12, 22, 25]) (cs := [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5, 17, 6, 7, 8, 0, 9, 10, 1, 1, 11, 18, 12, 13, 19, 0, 14, 0, 15, 1, 16]) (bs := [15, 3]) (W := 124000) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c81887_1 : P.sumLeaves 26 83852480 64 = 124000 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1310195) rows (by decide) (by decide)).symm.trans contract81887_1

theorem c81887_2 : P.sumLeaves 26 83852544 246 = 98003691 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81887) (lo := 256) (len := 246) (W := 98003691) check rows elimOK (by decide) (by decide) cover81887 (by decide)
  decide +kernel

theorem c81887_3 : P.sumLeaves 26 83852790 449 = 266784358 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81887) (lo := 502) (len := 449) (W := 266784358) check rows elimOK (by decide) (by decide) cover81887 (by decide)
  decide +kernel

theorem c81887_4 : P.sumLeaves 26 83853239 73 = 244865178 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81887) (lo := 951) (len := 73) (W := 244865178) check rows elimOK (by decide) (by decide) cover81887 (by decide)
  decide +kernel

theorem h81887 : P.leaf 36 81887 = 609851521 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(192, 74294), (64, 124000), (246, 98003691), (449, 266784358), (73, 244865178)]) (.cons c81887_0 (.cons c81887_1 (.cons c81887_2 (.cons c81887_3 (.cons c81887_4 (.nil)))))) (by decide) (by decide))

theorem cover81918 : P.CoversSplit 26 10 81918 0xfffffffafffffafafffffffafffffafafffffffafffcfac8aaaaaaaaaa88aa88fffffafafffffafaaaaaaaaaaaaaaaaafffffafafffcfac8aaaaaaaaaa88aa88fffffffafffffafafffffffafffffafafffffffaffccfac8aaaaaaaaaa88aa880000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [874, 930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f81918 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (83884032 + i)

theorem c81918_0 : rowSum f81918 0 468 = 313919746 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 81918) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover81918 (by decide)
  decide +kernel

theorem c81918_1 : rowSum f81918 468 242 = 410948238 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 81918) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover81918 (by decide)
  decide +kernel

theorem c81918_2 : rowSum f81918 710 210 = 561149830 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 81918) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover81918 (by decide)
  decide +kernel

theorem c81918_3 : rowSum f81918 920 104 = 669619438 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 81918) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover81918 (by decide)
  decide +kernel

theorem sum81918 : rowSum f81918 0 1024 = 1955637252 :=
  rowSum_append (F := f81918) (lo := 0) (n := 468) (m := 556) (A := 313919746) (B := 1641717506) c81918_0 (rowSum_append (F := f81918) (lo := 468) (n := 242) (m := 314) (A := 410948238) (B := 1230769268) c81918_1 (rowSum_append (F := f81918) (lo := 710) (n := 210) (m := 104) (A := 561149830) (B := 669619438) c81918_2 (c81918_3)))

theorem h81918 : P.leaf 36 81918 = 1955637252 :=
  leaf_weighted (k := 26) (d := 10) (H := 81918) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 81918) (by decide) (by decide +kernel)) sum81918

theorem cover81919 : P.CoversSplit 26 10 81919 0xfffffffafffffafafffffffafffffafafffffffafffcfac8aaaaaaaaaa88aa88fffffafafffffafaaaaaaaaaaaaaaaaafffffafafffcfac8aaaaaaaaaa88aa88fffffffafffffafafffffffafffffafafffffffaffccfac8aaaaaaaaaa88aa88fffffafafffffafaaaaaaaaaaaaaaaaafffffafaffccfac8aaaaaaaaaa88aa88 :=
  coversSplit check rows (by decide) (by decide) (xs := [930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f81919 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (83885056 + i)

theorem c81919_0 : rowSum f81919 0 252 = 13541904 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 81919) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover81919 (by decide)
  decide +kernel

theorem c81919_1 : rowSum f81919 252 208 = 536928241 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 81919) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover81919 (by decide)
  decide +kernel

theorem c81919_2 : rowSum f81919 460 245 = 751881272 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 81919) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover81919 (by decide)
  decide +kernel

theorem c81919_3 : rowSum f81919 705 211 = 995355532 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 81919) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover81919 (by decide)
  decide +kernel

theorem c81919_4 : rowSum f81919 916 108 = 1133823074 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 81919) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover81919 (by decide)
  decide +kernel

theorem sum81919 : rowSum f81919 0 1024 = 3431530023 :=
  rowSum_append (F := f81919) (lo := 0) (n := 252) (m := 772) (A := 13541904) (B := 3417988119) c81919_0 (rowSum_append (F := f81919) (lo := 252) (n := 208) (m := 564) (A := 536928241) (B := 2881059878) c81919_1 (rowSum_append (F := f81919) (lo := 460) (n := 245) (m := 319) (A := 751881272) (B := 2129178606) c81919_2 (rowSum_append (F := f81919) (lo := 705) (n := 211) (m := 108) (A := 995355532) (B := 1133823074) c81919_3 (c81919_4))))

theorem h81919 : P.leaf 36 81919 = 3431530023 :=
  leaf_weighted (k := 26) (d := 10) (H := 81919) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 81919) (by decide) (by decide +kernel)) sum81919

theorem cover88517 : P.CoversSplit 26 10 88517 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 531, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c88517_0 : P.sumLeaves 26 90641408 1024 = 34448 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88517) (lo := 0) (len := 1024) (W := 34448) check rows elimOK (by decide) (by decide) cover88517 (by decide)
  decide +kernel

theorem h88517 : P.leaf 36 88517 = 34448 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 34448)]) (.cons c88517_0 (.nil)) (by decide) (by decide))

theorem cover88519 : P.CoversSplit 26 10 88519 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 531, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c88519_0 : P.sumLeaves 26 90643456 1024 = 343632 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88519) (lo := 0) (len := 1024) (W := 343632) check rows elimOK (by decide) (by decide) cover88519 (by decide)
  decide +kernel

theorem h88519 : P.leaf 36 88519 = 343632 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 343632)]) (.cons c88519_0 (.nil)) (by decide) (by decide))

theorem cover88525 : P.CoversSplit 26 10 88525 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 922, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c88525_0 : P.sumLeaves 26 90649600 1024 = 70088 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88525) (lo := 0) (len := 1024) (W := 70088) check rows elimOK (by decide) (by decide) cover88525 (by decide)
  decide +kernel

theorem h88525 : P.leaf 36 88525 = 70088 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 70088)]) (.cons c88525_0 (.nil)) (by decide) (by decide))

theorem cover88527 : P.CoversSplit 26 10 88527 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c88527_0 : P.sumLeaves 26 90651648 1024 = 377552 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88527) (lo := 0) (len := 1024) (W := 377552) check rows elimOK (by decide) (by decide) cover88527 (by decide)
  decide +kernel

theorem h88527 : P.leaf 36 88527 = 377552 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 377552)]) (.cons c88527_0 (.nil)) (by decide) (by decide))

theorem cover88534 : P.CoversSplit 26 10 88534 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 531, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c88534_0 : P.sumLeaves 26 90658816 1024 = 3278990 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88534) (lo := 0) (len := 1024) (W := 3278990) check rows elimOK (by decide) (by decide) cover88534 (by decide)
  decide +kernel

theorem h88534 : P.leaf 36 88534 = 3278990 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3278990)]) (.cons c88534_0 (.nil)) (by decide) (by decide))

theorem cover88535 : P.CoversSplit 26 10 88535 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 531, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c88535_0 : P.sumLeaves 26 90659840 1024 = 3978058 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88535) (lo := 0) (len := 1024) (W := 3978058) check rows elimOK (by decide) (by decide) cover88535 (by decide)
  decide +kernel

theorem h88535 : P.leaf 36 88535 = 3978058 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3978058)]) (.cons c88535_0 (.nil)) (by decide) (by decide))

theorem cover88540 : P.CoversSplit 26 10 88540 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 922, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c88540_0 : P.sumLeaves 26 90664960 1024 = 500960 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88540) (lo := 0) (len := 1024) (W := 500960) check rows elimOK (by decide) (by decide) cover88540 (by decide)
  decide +kernel

theorem h88540 : P.leaf 36 88540 = 500960 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 500960)]) (.cons c88540_0 (.nil)) (by decide) (by decide))

theorem cover88541 : P.CoversSplit 26 10 88541 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 922, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c88541_0 : P.sumLeaves 26 90665984 1024 = 667612 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88541) (lo := 0) (len := 1024) (W := 667612) check rows elimOK (by decide) (by decide) cover88541 (by decide)
  decide +kernel

theorem h88541 : P.leaf 36 88541 = 667612 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 667612)]) (.cons c88541_0 (.nil)) (by decide) (by decide))

theorem cover88542 : P.CoversSplit 26 10 88542 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c88542_0 : P.sumLeaves 26 90667008 1024 = 4881826 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88542) (lo := 0) (len := 1024) (W := 4881826) check rows elimOK (by decide) (by decide) cover88542 (by decide)
  decide +kernel

theorem h88542 : P.leaf 36 88542 = 4881826 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4881826)]) (.cons c88542_0 (.nil)) (by decide) (by decide))

theorem cover88543 : P.CoversSplit 26 10 88543 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c88543_0 : P.sumLeaves 26 90668032 1024 = 5697700 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88543) (lo := 0) (len := 1024) (W := 5697700) check rows elimOK (by decide) (by decide) cover88543 (by decide)
  decide +kernel

theorem h88543 : P.leaf 36 88543 = 5697700 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5697700)]) (.cons c88543_0 (.nil)) (by decide) (by decide))

theorem cover88557 : P.CoversSplit 26 10 88557 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c88557_0 : P.sumLeaves 26 90682368 1024 = 139936 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88557) (lo := 0) (len := 1024) (W := 139936) check rows elimOK (by decide) (by decide) cover88557 (by decide)
  decide +kernel

theorem h88557 : P.leaf 36 88557 = 139936 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 139936)]) (.cons c88557_0 (.nil)) (by decide) (by decide))

theorem cover88558 : P.CoversSplit 26 10 88558 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c88558_0 : P.sumLeaves 26 90683392 1024 = 691008 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88558) (lo := 0) (len := 1024) (W := 691008) check rows elimOK (by decide) (by decide) cover88558 (by decide)
  decide +kernel

theorem h88558 : P.leaf 36 88558 = 691008 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 691008)]) (.cons c88558_0 (.nil)) (by decide) (by decide))

theorem cover88559 : P.CoversSplit 26 10 88559 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c88559_0 : P.sumLeaves 26 90684416 1024 = 737336 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88559) (lo := 0) (len := 1024) (W := 737336) check rows elimOK (by decide) (by decide) cover88559 (by decide)
  decide +kernel

theorem h88559 : P.leaf 36 88559 = 737336 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 737336)]) (.cons c88559_0 (.nil)) (by decide) (by decide))

theorem cover88574 : P.CoversSplit 26 10 88574 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c88574_0 : P.sumLeaves 26 90699776 1024 = 8794202 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88574) (lo := 0) (len := 1024) (W := 8794202) check rows elimOK (by decide) (by decide) cover88574 (by decide)
  decide +kernel

theorem h88574 : P.leaf 36 88574 = 8794202 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8794202)]) (.cons c88574_0 (.nil)) (by decide) (by decide))

theorem cover88575 : P.CoversSplit 26 10 88575 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c88575_0 : P.sumLeaves 26 90700800 1024 = 9370534 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88575) (lo := 0) (len := 1024) (W := 9370534) check rows elimOK (by decide) (by decide) cover88575 (by decide)
  decide +kernel

theorem h88575 : P.leaf 36 88575 = 9370534 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 9370534)]) (.cons c88575_0 (.nil)) (by decide) (by decide))

theorem cover88662 : P.CoversSplit 26 10 88662 0x8800000088020401000000000000000000000000000000000000000000000000000004000000040100000000000000000000000000000000000000000000000000000000002200010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 579, 587, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f88662 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (90789888 + i)

theorem c88662_0 : rowSum f88662 0 1024 = 519156 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 88662) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover88662 (by decide)
  decide +kernel

theorem sum88662 : rowSum f88662 0 1024 = 519156 :=
  c88662_0

theorem h88662 : P.leaf 36 88662 = 519156 :=
  leaf_weighted (k := 26) (d := 10) (H := 88662) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 88662) (by decide) (by decide +kernel)) sum88662

theorem cover88663 : P.CoversSplit 26 10 88663 0x8800000088020401000000000000000000000000000000000000000000000000000004000000040100000000000000000000000000000000000000000000000000000000002200010000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 579, 587, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f88663 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (90790912 + i)

theorem c88663_0 : rowSum f88663 0 1024 = 1106101 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 88663) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover88663 (by decide)
  decide +kernel

theorem sum88663 : rowSum f88663 0 1024 = 1106101 :=
  c88663_0

theorem h88663 : P.leaf 36 88663 = 1106101 :=
  leaf_weighted (k := 26) (d := 10) (H := 88663) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 88663) (by decide) (by decide +kernel)) sum88663

theorem cover88670 : P.CoversSplit 26 10 88670 0xaaaa0000aaa80504000000000000000000000000000000000000000000000500000005050000050400000000000000000000000000000000000000000000000000000000aa8805040000000000000000000000008800040000000000000004000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 579, 587, 874, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c88670_0 : P.sumLeaves 26 90798080 448 = 82592 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88670) (lo := 0) (len := 448) (W := 82592) check rows elimOK (by decide) (by decide) cover88670 (by decide)
  decide +kernel

theorem contract88670_1 : P.leaf 32 1418727 = 11928 := by
  apply (leaf_contract (k := 32) (b := 18) (H := 1418727) (ss := [(3, 1, 531), (4, 1, 580), (12, 1, 929), (18, 1, 1266), (20, 0, 1665), (8, 1, 529), (9, 0, 915), (15, 0, 915), (21, 1, 572), (11, 1, 872), (19, 0, 915), (29, 1, 573), (25, 1, 1258), (33, 0, 1259)]) (ids := [0, 3, 4, 5, 8, 11, 12, 14, 15, 20, 21, 22, 24, 25, 26, 28, 29, 30]) (cs := [2, 1, 1, 3, 4, 5, 1, 0, 6, 1, 1, 7, 8, 0, 9, 10, 1, 0, 0, 1, 11, 12, 13, 1, 14, 15, 16, 1, 17, 18, 19, 0]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c88670_1 : P.sumLeaves 26 90798528 64 = 11928 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1418727) rows (by decide) (by decide)).symm.trans contract88670_1

theorem c88670_2 : P.sumLeaves 26 90798592 192 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88670) (lo := 512) (len := 192) (W := 0) check rows elimOK (by decide) (by decide) cover88670 (by decide)
  decide +kernel

theorem contract88670_3 : P.leaf 32 1418731 = 0 := by
  exact leaf_contract_zero (ss := [(4, 1, 580), (12, 1, 929), (18, 1, 1266), (28, 0, 1315), (5, 1, 565), (9, 0, 579), (30, 0, 579), (32, 0, 579), (26, 1, 629), (15, 1, 922), (20, 1, 915), (19, 1, 1259), (21, 1, 1259)]) (q := 1658) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c88670_3 : P.sumLeaves 26 90798784 64 = 0 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1418731) rows (by decide) (by decide)).symm.trans contract88670_3

theorem c88670_4 : P.sumLeaves 26 90798848 256 = 1531576 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88670) (lo := 768) (len := 256) (W := 1531576) check rows elimOK (by decide) (by decide) cover88670 (by decide)
  decide +kernel

theorem h88670 : P.leaf 36 88670 = 1626096 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 82592), (64, 11928), (192, 0), (64, 0), (256, 1531576)]) (.cons c88670_0 (.cons c88670_1 (.cons c88670_2 (.cons c88670_3 (.cons c88670_4 (.nil)))))) (by decide) (by decide))

theorem cover88671 : P.CoversSplit 26 10 88671 0xaaaa0000aaa80504000000000000000000000000000000000000000000000500000005050000050400000000000000000000000000000000000000000000000000000000aa8805040000000000000000000000008800040000000000000004000000000000000504000000000000000000000000000004000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 579, 587, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c88671_0 : P.sumLeaves 26 90799104 448 = 99034 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88671) (lo := 0) (len := 448) (W := 99034) check rows elimOK (by decide) (by decide) cover88671 (by decide)
  decide +kernel

theorem contract88671_1 : P.leaf 32 1418743 = 27440 := by
  apply (leaf_contract (k := 32) (b := 18) (H := 1418743) (ss := [(3, 1, 531), (4, 1, 580), (12, 1, 929), (18, 1, 1266), (20, 0, 1665), (8, 1, 529), (9, 0, 915), (15, 0, 915), (21, 1, 572), (11, 1, 872), (19, 0, 915), (29, 1, 573), (25, 1, 1258), (33, 0, 1259)]) (ids := [0, 3, 4, 5, 8, 11, 12, 14, 15, 20, 21, 22, 24, 25, 26, 28, 29, 30]) (cs := [2, 1, 1, 3, 4, 5, 1, 0, 6, 1, 1, 7, 8, 0, 9, 10, 1, 0, 0, 1, 11, 12, 13, 1, 14, 15, 16, 1, 17, 18, 19, 0]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c88671_1 : P.sumLeaves 26 90799552 64 = 27440 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1418743) rows (by decide) (by decide)).symm.trans contract88671_1

theorem c88671_2 : P.sumLeaves 26 90799616 192 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88671) (lo := 512) (len := 192) (W := 0) check rows elimOK (by decide) (by decide) cover88671 (by decide)
  decide +kernel

theorem contract88671_3 : P.leaf 32 1418747 = 0 := by
  exact leaf_contract_zero (ss := [(4, 1, 580), (12, 1, 929), (18, 1, 1266), (28, 0, 1315), (5, 1, 565), (9, 0, 579), (30, 0, 579), (32, 0, 579), (26, 1, 629), (15, 1, 922), (20, 1, 915), (19, 1, 1259), (21, 1, 1259)]) (q := 1658) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c88671_3 : P.sumLeaves 26 90799808 64 = 0 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1418747) rows (by decide) (by decide)).symm.trans contract88671_3

theorem c88671_4 : P.sumLeaves 26 90799872 256 = 3332168 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88671) (lo := 768) (len := 256) (W := 3332168) check rows elimOK (by decide) (by decide) cover88671 (by decide)
  decide +kernel

theorem h88671 : P.leaf 36 88671 = 3458642 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 99034), (64, 27440), (192, 0), (64, 0), (256, 3332168)]) (.cons c88671_0 (.cons c88671_1 (.cons c88671_2 (.cons c88671_3 (.cons c88671_4 (.nil)))))) (by decide) (by decide))

theorem cover88702 : P.CoversSplit 26 10 88702 0xfffffffffffcfaf800000000000000000000000000000000000000000f0c0a080f0f0a0a0f0c0a080a0a0a0a0a080a080000000000000000000000000a080a0800000000ffccfac8000000000000000000000000ccccc8c8000000000c0c08080000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 587, 874, 922, 979, 1273, 1315, 1658, 1665]) (by decide +kernel)

noncomputable def f88702 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (90830848 + i)

theorem c88702_0 : rowSum f88702 0 1024 = 6784884 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 88702) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover88702 (by decide)
  decide +kernel

theorem sum88702 : rowSum f88702 0 1024 = 6784884 :=
  c88702_0

theorem h88702 : P.leaf 36 88702 = 6784884 :=
  leaf_weighted (k := 26) (d := 10) (H := 88702) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 88702) (by decide) (by decide +kernel)) sum88702

def seg : List (ℕ × ℕ) := [(81886, 720), (81887, 720), (81918, 180), (81919, 180), (88517, 360), (88519, 360), (88525, 720), (88527, 360), (88534, 180), (88535, 360), (88540, 720), (88541, 720), (88542, 720), (88543, 720), (88557, 360), (88558, 720), (88559, 720), (88574, 360), (88575, 360), (88662, 120), (88663, 120), (88670, 360), (88671, 360), (88702, 360)]

theorem segOK : checkSeg 20 perms 81886 88703 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 81886 88703 10860 1689116588220 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1689116588220)
    (SegSum.cons (w := 720) h81886 (SegSum.cons (w := 720) h81887 (SegSum.cons (w := 180) h81918 (SegSum.cons (w := 180) h81919 (SegSum.cons (w := 360) h88517 (SegSum.cons (w := 360) h88519 (SegSum.cons (w := 720) h88525 (SegSum.cons (w := 360) h88527 (SegSum.cons (w := 180) h88534 (SegSum.cons (w := 360) h88535 (SegSum.cons (w := 720) h88540 (SegSum.cons (w := 720) h88541 (SegSum.cons (w := 720) h88542 (SegSum.cons (w := 720) h88543 (SegSum.cons (w := 360) h88557 (SegSum.cons (w := 720) h88558 (SegSum.cons (w := 720) h88559 (SegSum.cons (w := 360) h88574 (SegSum.cons (w := 360) h88575 (SegSum.cons (w := 120) h88662 (SegSum.cons (w := 120) h88663 (SegSum.cons (w := 360) h88670 (SegSum.cons (w := 360) h88671 (SegSum.cons (w := 360) h88702 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S56
