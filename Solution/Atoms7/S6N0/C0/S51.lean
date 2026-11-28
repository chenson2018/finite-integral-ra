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

theorem cover302494 : P.CoversSplit 26 10 302494 0xffff050500330001000000000000000000000000000000000000000000000000555505050011000100000000000000000000000000000000000000000000000033330101003300010000000000000000000000000000000000000000000000001111010100110001000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 629, 636, 1265, 1266, 1272, 1273, 1658, 1665]) (by decide +kernel)

noncomputable def f302494 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (309753856 + i)

theorem c302494_0 : rowSum f302494 0 1024 = 10620031 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 302494) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover302494 (by decide)
  decide +kernel

theorem sum302494 : rowSum f302494 0 1024 = 10620031 :=
  c302494_0

theorem h302494 : P.leaf 36 302494 = 10620031 :=
  leaf_weighted (k := 26) (d := 10) (H := 302494) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 302494) (by decide) (by decide +kernel)) sum302494

theorem h81742 : P.leaf 36 81742 = 10620031 :=
  orient6 (v := 302494) (by decide) (by decide +kernel) h302494

theorem cover302495 : P.CoversSplit 26 10 302495 0xffff050500330001000000000000000000000000000000000000000000000000555505050011000100000000000000000000000000000000000000000000000033330101003300010000000000000000000000000000000000000000000000001111010100110001000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 629, 636, 1265, 1266, 1272, 1273, 1658, 1665]) (by decide +kernel)

noncomputable def f302495 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (309754880 + i)

theorem c302495_0 : rowSum f302495 0 1024 = 55435186 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 302495) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover302495 (by decide)
  decide +kernel

theorem sum302495 : rowSum f302495 0 1024 = 55435186 :=
  c302495_0

theorem h302495 : P.leaf 36 302495 = 55435186 :=
  leaf_weighted (k := 26) (d := 10) (H := 302495) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 302495) (by decide) (by decide +kernel)) sum302495

theorem h81743 : P.leaf 36 81743 = 55435186 :=
  orient6 (v := 302495) (by decide) (by decide +kernel) h302495

theorem cover302518 : P.CoversSplit 26 10 302518 0xcc00cc0000000000000000000000000000000000000000000000000000000000440044000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000033003300000000000000000000000000000000000000000000000000000000001100110000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 629, 636, 922, 923, 930, 1658]) (by decide +kernel)

theorem h302518 : P.leaf 36 302518 = 14712636 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 302518) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 302518) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 302518) (weight := rowWeight keep3 twice3) (xs := [64, 68, 80, 84, 320, 321, 324, 325, 336, 337, 340, 341, 746, 750, 762, 766, 1002, 1003, 1006, 1007, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover302518 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h81754 : P.leaf 36 81754 = 14712636 :=
  orient6 (v := 302518) (by decide) (by decide +kernel) h302518

theorem cover302519 : P.CoversSplit 26 10 302519 0xcc00cc0000000000000000000000000000000000000000000000000000000000440044000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000033003300000000000000000000000000000000000000000000000000000000001100110000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 629, 636, 922, 923, 930, 1658]) (by decide +kernel)

theorem h302519 : P.leaf 36 302519 = 27153515 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 302519) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 302519) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 302519) (weight := rowWeight keep3 twice3) (xs := [64, 68, 80, 84, 320, 321, 324, 325, 336, 337, 340, 341, 746, 750, 762, 766, 1002, 1003, 1006, 1007, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover302519 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h81755 : P.leaf 36 81755 = 27153515 :=
  orient6 (v := 302519) (by decide) (by decide +kernel) h302519

theorem cover302522 : P.CoversSplit 26 10 302522 0xf0f0f5f500300030000000000000000000000000000000000000000000000000505055550010001000000000000000000000000000000000000000000000000030303131003000300000000000000000000000000000000000000000000000001010111100100010000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [481, 538, 629, 636, 922, 929, 1265, 1266, 1273, 1658, 1665]) (ps := [(15, [930], [922])]) (by decide +kernel)

noncomputable def f302522 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (309782528 + i)

theorem c302522_0 : rowSum f302522 0 1024 = 21222628 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 302522) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover302522 (by decide)
  decide +kernel

theorem sum302522 : rowSum f302522 0 1024 = 21222628 :=
  c302522_0

theorem h302522 : P.leaf 36 302522 = 21222628 :=
  leaf_weighted (k := 26) (d := 10) (H := 302522) (keep := keep4) (twice := twice4) rows (by decide) (by decide) (bal4) (invRow4 (H := 302522) (by decide) (by decide +kernel)) sum302522

theorem h81756 : P.leaf 36 81756 = 21222628 :=
  orient6 (v := 302522) (by decide) (by decide +kernel) h302522

theorem cover302523 : P.CoversSplit 26 10 302523 0xf0f0f5f500300030000000000000000000000000000000000000000000000000505055550010001000000000000000000000000000000000000000000000000030303131003000300000000000000000000000000000000000000000000000001010111100100010000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [481, 538, 629, 636, 922, 929, 1265, 1266, 1273, 1658, 1665]) (ps := [(15, [930], [922])]) (by decide +kernel)

noncomputable def f302523 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (309783552 + i)

theorem c302523_0 : rowSum f302523 0 1024 = 37840272 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 302523) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover302523 (by decide)
  decide +kernel

theorem sum302523 : rowSum f302523 0 1024 = 37840272 :=
  c302523_0

theorem h302523 : P.leaf 36 302523 = 37840272 :=
  leaf_weighted (k := 26) (d := 10) (H := 302523) (keep := keep4) (twice := twice4) rows (by decide) (by decide) (bal4) (invRow4 (H := 302523) (by decide) (by decide +kernel)) sum302523

theorem h81757 : P.leaf 36 81757 = 37840272 :=
  orient6 (v := 302523) (by decide) (by decide +kernel) h302523

theorem cover302526 : P.CoversSplit 26 10 302526 0xffffffff00330032000000000000000000000000000000000000000000000000555555550011001000000000000000000000000000000000000000000000000033333333003300320000000000000000003300330000000000000000000000001111111100110010000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [538, 629, 636, 922, 930, 1266, 1273, 1658, 1665]) (ps := [(19, [1265], [1273]), (21, [867], [1658])]) (by decide +kernel)

theorem c302526_0 : P.sumLeaves 26 309786624 1020 = 76757838 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 302526) (lo := 0) (len := 1020) (W := 76757838) check rows elimOK (by decide) (by decide) cover302526 (by decide)
  decide +kernel

theorem c302526_1 : P.sumLeaves 26 309787644 4 = 12608680 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 302526) (lo := 1020) (len := 4) (W := 12608680) check rows elimOK (by decide) (by decide) cover302526 (by decide)
  decide +kernel

theorem h302526 : P.leaf 36 302526 = 89366518 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1020, 76757838), (4, 12608680)]) (.cons c302526_0 (.cons c302526_1 (.nil))) (by decide) (by decide))

theorem h81758 : P.leaf 36 81758 = 89366518 :=
  orient6 (v := 302526) (by decide) (by decide +kernel) h302526

theorem cover302527 : P.CoversSplit 26 10 302527 0xffffffff00330032000000000000000000000000000000000000000000000000555555550011001000000000000000000000000000000000000000000000000033333333003300320000000000000000003300330000000000000000000000001111111100110010000000000000000000110011000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [538, 629, 636, 922, 930, 1266, 1273, 1658, 1665]) (ps := [(19, [1265], [1273])]) (by decide +kernel)

theorem c302527_0 : P.sumLeaves 26 309787648 1016 = 110759059 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 302527) (lo := 0) (len := 1016) (W := 110759059) check rows elimOK (by decide) (by decide) cover302527 (by decide)
  decide +kernel

theorem c302527_1 : P.sumLeaves 26 309788664 8 = 37365460 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 302527) (lo := 1016) (len := 8) (W := 37365460) check rows elimOK (by decide) (by decide) cover302527 (by decide)
  decide +kernel

theorem h302527 : P.leaf 36 302527 = 148124519 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1016, 110759059), (8, 37365460)]) (.cons c302527_0 (.cons c302527_1 (.nil))) (by decide) (by decide))

theorem h81759 : P.leaf 36 81759 = 148124519 :=
  orient6 (v := 302527) (by decide) (by decide +kernel) h302527

theorem cover302590 : P.CoversSplit 26 10 302590 0xffffffffffffffff000000000000000000000000000000001111101011001000555555555555555555555050555550500000000000000000111110101100100033333333333333330000000000000000333333333300330011111010110010001111111111111111000000000000000000000000000000001111101011001000 :=
  coversProjected check rows (by decide) (by decide) (xs := [629, 636, 922, 930, 1658, 1665]) (ps := [(20, [866], [1665]), (21, [867], [1658])]) (by decide +kernel)

noncomputable def f302590 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (309852160 + i)

theorem c302590_0 : rowSum f302590 0 975 = 152260702 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 302590) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover302590 (by decide)
  decide +kernel

theorem c302590_1 : rowSum f302590 975 49 = 197191618 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 302590) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover302590 (by decide)
  decide +kernel

theorem sum302590 : rowSum f302590 0 1024 = 349452320 :=
  rowSum_append (F := f302590) (lo := 0) (n := 975) (m := 49) (A := 152260702) (B := 197191618) c302590_0 (c302590_1)

theorem h302590 : P.leaf 36 302590 = 349452320 :=
  leaf_weighted (k := 26) (d := 10) (H := 302590) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 302590) (by decide) (by decide +kernel)) sum302590

theorem h81790 : P.leaf 36 81790 = 349452320 :=
  orient6 (v := 302590) (by decide) (by decide +kernel) h302590

theorem cover302591 : P.CoversSplit 26 10 302591 0xffffffffffffffff000000000000000000000000000000001111101011001000555555555555555555555050555550500000000000000000111110101100100033333333333333330000000000000000333333333300330011111010110010001111111111111111111110101111101011111111110011001111101011001000 :=
  coversSplit check rows (by decide) (by decide) (xs := [629, 636, 922, 930, 1658, 1665]) (by decide +kernel)

noncomputable def f302591 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (309853184 + i)

theorem c302591_0 : rowSum f302591 0 816 = 175293290 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 302591) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover302591 (by decide)
  decide +kernel

theorem c302591_1 : rowSum f302591 816 208 = 373090941 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 302591) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover302591 (by decide)
  decide +kernel

theorem sum302591 : rowSum f302591 0 1024 = 548384231 :=
  rowSum_append (F := f302591) (lo := 0) (n := 816) (m := 208) (A := 175293290) (B := 373090941) c302591_0 (c302591_1)

theorem h302591 : P.leaf 36 302591 = 548384231 :=
  leaf_weighted (k := 26) (d := 10) (H := 302591) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 302591) (by decide) (by decide +kernel)) sum302591

theorem h81791 : P.leaf 36 81791 = 548384231 :=
  orient6 (v := 302591) (by decide) (by decide +kernel) h302591

theorem cover81811 : P.CoversSplit 26 10 81811 0xc000000000000000c0000000000000000000000000000000000000000000000000000c000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 538, 608, 930, 972, 979, 1315]) (by decide +kernel)

theorem h81811 : P.leaf 36 81811 = 4354144 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81811) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81811) (weight := fun _ => 1) (xs := [683, 746, 747, 958, 959, 1022, 1023]) check rows elimOK (by decide) (by decide) cover81811 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover855195 : P.CoversSplit 26 10 855195 0x8000800000000000800080000000000000000000000000000000000000000000800080000000000080008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 537, 538, 587, 636, 881, 929, 1273]) (by decide +kernel)

theorem h855195 : P.leaf 36 855195 = 949522 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 855195) (keep := keep9) (twice := twice9) rows (by decide) (by decide) bal9 (invRow9 (H := 855195) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 855195) (weight := rowWeight keep9 twice9) (xs := [687, 703, 751, 767, 943, 959, 1007, 1023]) check rows elimOK (by decide) (by decide) cover855195 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h81812 : P.leaf 36 81812 = 949522 :=
  orient85 (v := 855195) (by decide) (by decide +kernel) h855195

theorem cover855199 : P.CoversSplit 26 10 855199 0x8000800000000000800080000000000000000000000000000000000000000000800080000000000080008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 537, 538, 587, 636, 881, 929, 1273]) (by decide +kernel)

theorem h855199 : P.leaf 36 855199 = 3518552 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 855199) (keep := keep9) (twice := twice9) rows (by decide) (by decide) bal9 (invRow9 (H := 855199) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 855199) (weight := rowWeight keep9 twice9) (xs := [687, 703, 751, 767, 943, 959, 1007, 1023]) check rows elimOK (by decide) (by decide) cover855199 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h81813 : P.leaf 36 81813 = 3518552 :=
  orient85 (v := 855199) (by decide) (by decide +kernel) h855199

theorem cover109939 : P.CoversSplit 26 10 109939 0x8800880000000000880088000000000000000000000000000000000000000000000000000000000000008800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 608, 629, 636, 881, 930, 1273, 1322]) (by decide +kernel)

theorem h109939 : P.leaf 36 109939 = 3333644 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 109939) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 109939) (weight := fun _ => 1) (xs := [683, 687, 939, 943, 955, 959, 1003, 1007, 1019, 1023]) check rows elimOK (by decide) (by decide) cover109939 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h81814 : P.leaf 36 81814 = 3333644 :=
  orient72 (v := 109939) (by decide) (by decide +kernel) h109939

theorem cover81815 : P.CoversSplit 26 10 81815 0xcc00000000000000cc00000000000000000000000000000000000000000000000c0000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 930, 972, 979, 1315, 1658, 1665]) (by decide +kernel)

theorem h81815 : P.leaf 36 81815 = 14272764 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81815) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81815) (weight := fun _ => 1) (xs := [699, 762, 763, 954, 955, 958, 959, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover81815 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover81816 : P.CoversSplit 26 10 81816 0xf0f0000000000000f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 538, 615, 923, 972, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem h81816 : P.leaf 36 81816 = 502528 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81816) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81816) (weight := fun _ => 1) (xs := [309, 372, 373, 948, 949, 950, 951, 956, 957, 958, 959, 1012, 1013, 1014, 1015, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover81816 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover81817 : P.CoversSplit 26 10 81817 0xf0f0000000000000f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 538, 615, 923, 972, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem h81817 : P.leaf 36 81817 = 9870724 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81817) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81817) (weight := fun _ => 1) (xs := [309, 372, 373, 948, 949, 950, 951, 956, 957, 958, 959, 1012, 1013, 1014, 1015, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover81817 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover81818 : P.CoversSplit 26 10 81818 0xf0f0000000000000f0f000000000000000000000000000000000000000000000000005050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000000000000200000000000000000000000000000000000000000000000000001000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 538, 615, 972, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem h81818 : P.leaf 36 81818 = 8286110 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81818) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81818) (weight := fun _ => 1) (xs := [96, 309, 372, 373, 736, 738, 744, 746, 948, 949, 950, 951, 956, 957, 958, 959, 1012, 1013, 1014, 1015, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover81818 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover81819 : P.CoversSplit 26 10 81819 0xf0f0000000000000f0f000000000000000000000000000000000000000000000000005050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000000000000200000000000000000000000000000000000000000000000000001000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 538, 615, 972, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem h81819 : P.leaf 36 81819 = 26211328 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81819) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81819) (weight := fun _ => 1) (xs := [96, 309, 372, 373, 736, 738, 744, 746, 948, 949, 950, 951, 956, 957, 958, 959, 1012, 1013, 1014, 1015, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover81819 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover81820 : P.CoversSplit 26 10 81820 0xffff000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003300000000000000220000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 923, 930, 972, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c81820_0 : P.sumLeaves 26 83783680 1024 = 8403120 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81820) (lo := 0) (len := 1024) (W := 8403120) check rows elimOK (by decide) (by decide) cover81820 (by decide)
  decide +kernel

theorem h81820 : P.leaf 36 81820 = 8403120 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8403120)]) (.cons c81820_0 (.nil)) (by decide) (by decide))

theorem cover81821 : P.CoversSplit 26 10 81821 0xffff000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003300000000000000220000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 923, 930, 972, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c81821_0 : P.sumLeaves 26 83784704 1024 = 34607802 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81821) (lo := 0) (len := 1024) (W := 34607802) check rows elimOK (by decide) (by decide) cover81821 (by decide)
  decide +kernel

theorem h81821 : P.leaf 36 81821 = 34607802 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 34607802)]) (.cons c81821_0 (.nil)) (by decide) (by decide))

theorem cover109947 : P.CoversSplit 26 10 109947 0xaaaaaaaa00000000aaaaabab0000000000000000000000000000000000000022000000000000000000000a0a000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 629, 636, 1322, 1658, 1665]) (by decide +kernel)

theorem c109947_0 : P.sumLeaves 26 112585728 1024 = 27650916 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 109947) (lo := 0) (len := 1024) (W := 27650916) check rows elimOK (by decide) (by decide) cover109947 (by decide)
  decide +kernel

theorem h109947 : P.leaf 36 109947 = 27650916 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 27650916)]) (.cons c109947_0 (.nil)) (by decide) (by decide))

theorem h81822 : P.leaf 36 81822 = 27650916 :=
  orient72 (v := 109947) (by decide) (by decide +kernel) h109947

theorem cover81823 : P.CoversSplit 26 10 81823 0xffff000000000000ffff000000000000000000000000000000000000000000000f0f0a0a000000000a0a0a0a000000000000000000000000000000000000000000000000000000000000000000000000003300000000000000220000000000000000000000000000000000000000000000030002000000000002000200000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 972, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c81823_0 : P.sumLeaves 26 83786752 1024 = 77338324 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81823) (lo := 0) (len := 1024) (W := 77338324) check rows elimOK (by decide) (by decide) cover81823 (by decide)
  decide +kernel

theorem h81823 : P.leaf 36 81823 = 77338324 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 77338324)]) (.cons c81823_0 (.nil)) (by decide) (by decide))

theorem cover110067 : P.CoversSplit 26 10 110067 0x8800880000000000880088000000000000000000000000000000000000000000000000000000000000008800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 608, 629, 636, 881, 930, 1273, 1322]) (by decide +kernel)

theorem h110067 : P.leaf 36 110067 = 17990104 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 110067) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 110067) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 110067) (weight := rowWeight keep1 twice1) (xs := [683, 687, 939, 943, 955, 959, 1003, 1007, 1019, 1023]) check rows elimOK (by decide) (by decide) cover110067 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h81846 : P.leaf 36 81846 = 17990104 :=
  orient72 (v := 110067) (by decide) (by decide +kernel) h110067

theorem cover863423 : P.CoversSplit 26 10 863423 0xcc00cc0000000000cc00cc000000000000000000000000000000000000000000c800c80000000000c800c800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 587, 629, 636, 881, 1273]) (by decide +kernel)

theorem h863423 : P.leaf 36 863423 = 73773806 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 863423) (keep := keep9) (twice := twice9) rows (by decide) (by decide) bal9 (invRow9 (H := 863423) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 863423) (weight := rowWeight keep9 twice9) (xs := [683, 686, 687, 699, 702, 703, 747, 750, 751, 763, 766, 767, 938, 939, 942, 943, 954, 955, 958, 959, 1002, 1003, 1006, 1007, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover863423 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h81847 : P.leaf 36 81847 = 73773806 :=
  orient85 (v := 863423) (by decide) (by decide +kernel) h863423

theorem cover110419 : P.CoversSplit 26 10 110419 0xaa00000000000000000000000000000000000000000000000000000000000000aa0000000000000000000a000000000000000000000000000000000000000000aa00000000000000000000000000000000000000220000000000000000000000aa0000000000000000000a000000000000000000220000000000000000000200 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 530, 579, 881, 930]) (by decide +kernel)

theorem h110419 : P.leaf 36 110419 = 1768443 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 110419) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 110419) (weight := fun _ => 1) (xs := [9, 89, 93, 169, 171, 249, 251, 253, 255, 345, 349, 505, 507, 509, 511, 681, 683, 761, 763, 765, 767, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover110419 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h81848 : P.leaf 36 81848 = 1768443 :=
  orient84 (v := 110419) (by decide) (by decide +kernel) h110419

theorem cover81849 : P.CoversSplit 26 10 81849 0xf0f0f0f500000000f0f0f0f50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000310000000000200020000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 923, 930, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c81849_0 : P.sumLeaves 26 83813376 1024 = 60253869 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81849) (lo := 0) (len := 1024) (W := 60253869) check rows elimOK (by decide) (by decide) cover81849 (by decide)
  decide +kernel

theorem h81849 : P.leaf 36 81849 = 60253869 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 60253869)]) (.cons c81849_0 (.nil)) (by decide) (by decide))

theorem cover110073 : P.CoversSplit 26 10 110073 0xaaaaaaaa00000000aaaaabab0000000000000000000000000000000000000022000000000000000000000a0a000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 580, 629, 636, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c110073_0 : P.sumLeaves 26 112714752 1024 = 42922789 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 110073) (lo := 0) (len := 1024) (W := 42922789) check rows elimOK (by decide) (by decide) cover110073 (by decide)
  decide +kernel

theorem h110073 : P.leaf 36 110073 = 42922789 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 42922789)]) (.cons c110073_0 (.nil)) (by decide) (by decide))

theorem h81850 : P.leaf 36 81850 = 42922789 :=
  orient72 (v := 110073) (by decide) (by decide +kernel) h110073

theorem cover81851 : P.CoversSplit 26 10 81851 0xf0f0f0f500000000f0f0f0f50000000000000000000000000000000000000000000050500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000310000000000200020000000000000000000000000000000000000000000000010000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c81851_0 : P.sumLeaves 26 83815424 1024 = 134977234 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81851) (lo := 0) (len := 1024) (W := 134977234) check rows elimOK (by decide) (by decide) cover81851 (by decide)
  decide +kernel

theorem h81851 : P.leaf 36 81851 = 134977234 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 134977234)]) (.cons c81851_0 (.nil)) (by decide) (by decide))

theorem cover110075 : P.CoversSplit 26 10 110075 0xaaaaaaaa00000000aaaaabab0000000000000000000000000000000000000022000000000000000000000a0a000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 629, 636, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f110075 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (112716800 + i)

theorem c110075_0 : rowSum f110075 0 1024 = 169465770 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 110075) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover110075 (by decide)
  decide +kernel

theorem sum110075 : rowSum f110075 0 1024 = 169465770 :=
  c110075_0

theorem h110075 : P.leaf 36 110075 = 169465770 :=
  leaf_weighted (k := 26) (d := 10) (H := 110075) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 110075) (by decide) (by decide +kernel)) sum110075

theorem h81854 : P.leaf 36 81854 = 169465770 :=
  orient72 (v := 110075) (by decide) (by decide +kernel) h110075

theorem cover110079 : P.CoversSplit 26 10 110079 0xffffffff00000000fffffefe0000000000000000000000000000000000000022ffffaaaa00000000aaaaaaaa000000000000000000000000000000000000002200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [629, 636, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f110079 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (112720896 + i)

theorem c110079_0 : rowSum f110079 0 1024 = 445572363 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 110079) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover110079 (by decide)
  decide +kernel

theorem sum110079 : rowSum f110079 0 1024 = 445572363 :=
  c110079_0

theorem h110079 : P.leaf 36 110079 = 445572363 :=
  leaf_weighted (k := 26) (d := 10) (H := 110079) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 110079) (by decide) (by decide +kernel)) sum110079

theorem h81855 : P.leaf 36 81855 = 445572363 :=
  orient72 (v := 110079) (by decide) (by decide +kernel) h110079

theorem cover302994 : P.CoversSplit 26 10 302994 0xf000040000200000000000000000000000000000000000000000000000000000f000040000200000000000000000000000000000000000000000000000000000f000040000200000000000000000000000000000000000000000000000000000f000040000200000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [481, 489, 530, 538, 608, 615, 922, 929, 930, 1265, 1273]) (ps := [(7, [467], [482])]) (by decide +kernel)

theorem h302994 : P.leaf 36 302994 = 984000 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 302994) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 302994) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 302994) (weight := rowWeight keep0 twice0) (xs := [213, 234, 252, 253, 254, 255, 469, 490, 508, 509, 510, 511, 725, 746, 764, 765, 766, 767, 981, 1002, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover302994 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h81864 : P.leaf 36 81864 = 984000 :=
  orient6 (v := 302994) (by decide) (by decide +kernel) h302994

def seg : List (ℕ × ℕ) := [(81742, 360), (81743, 360), (81754, 360), (81755, 360), (81756, 360), (81757, 360), (81758, 720), (81759, 720), (81790, 180), (81791, 180), (81811, 360), (81812, 360), (81813, 360), (81814, 720), (81815, 720), (81816, 720), (81817, 720), (81818, 720), (81819, 720), (81820, 720), (81821, 720), (81822, 720), (81823, 720), (81846, 180), (81847, 180), (81848, 360), (81849, 360), (81850, 720), (81851, 720), (81854, 360), (81855, 360), (81864, 90)]

theorem segOK : checkSeg 20 perms 81742 81865 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 81742 81865 15570 935873928540 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 935873928540)
    (SegSum.cons (w := 360) h81742 (SegSum.cons (w := 360) h81743 (SegSum.cons (w := 360) h81754 (SegSum.cons (w := 360) h81755 (SegSum.cons (w := 360) h81756 (SegSum.cons (w := 360) h81757 (SegSum.cons (w := 720) h81758 (SegSum.cons (w := 720) h81759 (SegSum.cons (w := 180) h81790 (SegSum.cons (w := 180) h81791 (SegSum.cons (w := 360) h81811 (SegSum.cons (w := 360) h81812 (SegSum.cons (w := 360) h81813 (SegSum.cons (w := 720) h81814 (SegSum.cons (w := 720) h81815 (SegSum.cons (w := 720) h81816 (SegSum.cons (w := 720) h81817 (SegSum.cons (w := 720) h81818 (SegSum.cons (w := 720) h81819 (SegSum.cons (w := 720) h81820 (SegSum.cons (w := 720) h81821 (SegSum.cons (w := 720) h81822 (SegSum.cons (w := 720) h81823 (SegSum.cons (w := 180) h81846 (SegSum.cons (w := 180) h81847 (SegSum.cons (w := 360) h81848 (SegSum.cons (w := 360) h81849 (SegSum.cons (w := 720) h81850 (SegSum.cons (w := 720) h81851 (SegSum.cons (w := 360) h81854 (SegSum.cons (w := 360) h81855 (SegSum.cons (w := 90) h81864 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S51
