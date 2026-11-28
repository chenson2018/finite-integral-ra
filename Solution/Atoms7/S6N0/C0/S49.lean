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

namespace RACert.S6N0.C0.S49

open RACert RACert.Problem

theorem cover276987 : P.CoversSplit 26 10 276987 0xfffffffafffffffa000000000000000000000000000000000011000000000000000000000000000000000000000000000000000000000000000000000000000000330032003300320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 629, 636, 923, 930, 972, 979, 1265, 1273, 1658, 1665]) (by decide +kernel)

theorem c276987_0 : P.sumLeaves 26 283634688 1024 = 70952410 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 276987) (lo := 0) (len := 1024) (W := 70952410) check rows elimOK (by decide) (by decide) cover276987 (by decide)
  decide +kernel

theorem h276987 : P.leaf 36 276987 = 70952410 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 70952410)]) (.cons c276987_0 (.nil)) (by decide) (by decide))

theorem h79838 : P.leaf 36 79838 = 70952410 :=
  orient74 (v := 276987) (by decide) (by decide +kernel) h276987

theorem cover276991 : P.CoversSplit 26 10 276991 0xfffffffafffffffa000000000000000000000000000000000011000000000000000000000000000000000000000000000000000000000000000000000000000000330032003300320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [629, 636, 923, 930, 972, 979, 1265, 1273, 1658, 1665]) (by decide +kernel)

theorem c276991_0 : P.sumLeaves 26 283638784 1024 = 188659629 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 276991) (lo := 0) (len := 1024) (W := 188659629) check rows elimOK (by decide) (by decide) cover276991 (by decide)
  decide +kernel

theorem h276991 : P.leaf 36 276991 = 188659629 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 188659629)]) (.cons c276991_0 (.nil)) (by decide) (by decide))

theorem h79839 : P.leaf 36 79839 = 188659629 :=
  orient74 (v := 276991) (by decide) (by decide +kernel) h276991

theorem cover80858 : P.CoversSplit 26 10 80858 0xf0f00000f0f00005f0f00000f0f00005000000000000000000000000000000000000050500000505000000000000000000000000000000000000000000000000f0f00000f0f00005f0f00000f0f00005000000000000000000000000000000000000050500000505000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 867, 972, 1315]) (by decide +kernel)

noncomputable def f80858 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (82798592 + i)

theorem c80858_0 : rowSum f80858 0 1024 = 44646644 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 80858) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover80858 (by decide)
  decide +kernel

theorem sum80858 : rowSum f80858 0 1024 = 44646644 :=
  c80858_0

theorem h80858 : P.leaf 36 80858 = 44646644 :=
  leaf_weighted (k := 26) (d := 10) (H := 80858) (keep := keep3) (twice := twice3) rows (by decide) (by decide) (bal3) (invRow3 (H := 80858) (by decide) (by decide +kernel)) sum80858

theorem h79852 : P.leaf 36 79852 = 44646644 :=
  orient4 (v := 80858) (by decide) (by decide +kernel) h80858

theorem cover298971 : P.CoversSplit 26 10 298971 0xf0f00505f0f00504000005050000050500000000000000000000000000000000f0f00505f0f00504000000000000000000000000000000000000000000000000f0f00505f0f00504000005050000050500000000000000000000000000000000f0f00505f0f00504000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [481, 881, 922, 929, 1265]) (ps := [(15, [930], [922])]) (by decide +kernel)

noncomputable def f298971 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (306146304 + i)

theorem c298971_0 : rowSum f298971 0 1024 = 109525488 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 298971) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover298971 (by decide)
  decide +kernel

theorem sum298971 : rowSum f298971 0 1024 = 109525488 :=
  c298971_0

theorem h298971 : P.leaf 36 298971 = 109525488 :=
  leaf_weighted (k := 26) (d := 10) (H := 298971) (keep := keep3) (twice := twice3) rows (by decide) (by decide) (bal3) (invRow3 (H := 298971) (by decide) (by decide +kernel)) sum298971

theorem h79853 : P.leaf 36 79853 = 109525488 :=
  orient6 (v := 298971) (by decide) (by decide +kernel) h298971

theorem cover80862 : P.CoversSplit 26 10 80862 0xffff0000ffff0500ffff0000ffff0500000000000000000000000000000000000505000005050000000000000000000000000000000000000000000000000000ffff0000ffff0500ffff0000ffff0500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 867, 880, 972, 1315, 1658]) (by decide +kernel)

theorem c80862_0 : P.sumLeaves 26 82802688 946 = 59489724 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 80862) (lo := 0) (len := 946) (W := 59489724) check rows elimOK (by decide) (by decide) cover80862 (by decide)
  decide +kernel

theorem c80862_1 : P.sumLeaves 26 82803634 78 = 94538284 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 80862) (lo := 946) (len := 78) (W := 94538284) check rows elimOK (by decide) (by decide) cover80862 (by decide)
  decide +kernel

theorem h80862 : P.leaf 36 80862 = 154028008 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(946, 59489724), (78, 94538284)]) (.cons c80862_0 (.cons c80862_1 (.nil))) (by decide) (by decide))

theorem h79854 : P.leaf 36 79854 = 154028008 :=
  orient4 (v := 80862) (by decide) (by decide +kernel) h80862

theorem cover298975 : P.CoversSplit 26 10 298975 0xffff0505ffff0504050500000505000000000000000000000000000000000000ffff0505ffff0504000000000000000000000000000000000000000000000000ffff0505ffff0504050500000505000000000000000000000000000000000000ffff0505ffff0504000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [530, 881, 922, 930, 1265, 1272, 1658]) (ps := [(19, [1273], [1265])]) (by decide +kernel)

theorem c298975_0 : P.sumLeaves 26 306150400 727 = 187948130 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 298975) (lo := 0) (len := 727) (W := 187948130) check rows elimOK (by decide) (by decide) cover298975 (by decide)
  decide +kernel

theorem c298975_1 : P.sumLeaves 26 306151127 297 = 227653905 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 298975) (lo := 727) (len := 297) (W := 227653905) check rows elimOK (by decide) (by decide) cover298975 (by decide)
  decide +kernel

theorem h298975 : P.leaf 36 298975 = 415602035 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(727, 187948130), (297, 227653905)]) (.cons c298975_0 (.cons c298975_1 (.nil))) (by decide) (by decide))

theorem h79855 : P.leaf 36 79855 = 415602035 :=
  orient6 (v := 298975) (by decide) (by decide +kernel) h298975

theorem cover80894 : P.CoversSplit 26 10 80894 0xfffffffafffffafafffffffafffffafa00000000000000000000000000000000fffffafafffffafaaaaaaaaaaaaaaaaa00000000000000000000000000000000fffffffafffffafafffffffafffffafa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [867, 874, 972, 1315, 1658]) (by decide +kernel)

noncomputable def f80894 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (82835456 + i)

theorem c80894_0 : rowSum f80894 0 710 = 286928762 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 80894) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover80894 (by decide)
  decide +kernel

theorem c80894_1 : rowSum f80894 710 296 = 514079774 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 80894) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover80894 (by decide)
  decide +kernel

theorem c80894_2 : rowSum f80894 1006 18 = 75328394 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 80894) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover80894 (by decide)
  decide +kernel

theorem sum80894 : rowSum f80894 0 1024 = 876336930 :=
  rowSum_append (F := f80894) (lo := 0) (n := 710) (m := 314) (A := 286928762) (B := 589408168) c80894_0 (rowSum_append (F := f80894) (lo := 710) (n := 296) (m := 18) (A := 514079774) (B := 75328394) c80894_1 (c80894_2))

theorem h80894 : P.leaf 36 80894 = 876336930 :=
  leaf_weighted (k := 26) (d := 10) (H := 80894) (keep := keep3) (twice := twice3) rows (by decide) (by decide) (bal3) (invRow3 (H := 80894) (by decide) (by decide +kernel)) sum80894

theorem h79870 : P.leaf 36 79870 = 876336930 :=
  orient4 (v := 80894) (by decide) (by decide +kernel) h80894

theorem cover564223 : P.CoversSplit 26 10 564223 0xfffffffffffffac8fafaaaaafafaaa88ffccffccccccc8c8fac8aa88c8c88888fffffafafffffac8fafaaaaafafaaa88ffccfac8ccccc8c8fac8aa88c8c88888ffffffffffccfac8fafaaaaafac8aa88ffccffccccccc8c8fac8aa88c8c88888fffffafaffccfac8fafaaaaafac8aa88ffccfac8ccccc8c8fac8aa88c8c88888 :=
  coversSplit check rows (by decide) (by decide) (xs := [922, 930, 1265, 1273, 1315, 1322]) (by decide +kernel)

noncomputable def f564223 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (577764352 + i)

theorem c564223_0 : rowSum f564223 0 311 = 699487765 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 564223) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover564223 (by decide)
  decide +kernel

theorem c564223_1 : rowSum f564223 311 164 = 821261522 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 564223) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover564223 (by decide)
  decide +kernel

theorem c564223_2 : rowSum f564223 475 501 = 902050618 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 564223) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover564223 (by decide)
  decide +kernel

theorem c564223_3 : rowSum f564223 976 48 = 281900720 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 564223) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover564223 (by decide)
  decide +kernel

theorem sum564223 : rowSum f564223 0 1024 = 2704700625 :=
  rowSum_append (F := f564223) (lo := 0) (n := 311) (m := 713) (A := 699487765) (B := 2005212860) c564223_0 (rowSum_append (F := f564223) (lo := 311) (n := 164) (m := 549) (A := 821261522) (B := 1183951338) c564223_1 (rowSum_append (F := f564223) (lo := 475) (n := 501) (m := 48) (A := 902050618) (B := 281900720) c564223_2 (c564223_3)))

theorem h564223 : P.leaf 36 564223 = 2704700625 :=
  leaf_weighted (k := 26) (d := 10) (H := 564223) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 564223) (by decide) (by decide +kernel)) sum564223

theorem h79871 : P.leaf 36 79871 = 2704700625 :=
  orient324 (v := 564223) (by decide) (by decide +kernel) h564223

theorem cover81150 : P.CoversSplit 26 10 81150 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000100000000002000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 580, 587, 629, 636, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem h81150 : P.leaf 36 81150 = 408104 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81150) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81150) (weight := fun _ => 1) (xs := [256, 277, 320, 341, 1023]) check rows elimOK (by decide) (by decide) cover81150 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover81151 : P.CoversSplit 26 10 81151 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000100000000002000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 580, 587, 629, 636, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem h81151 : P.leaf 36 81151 = 454112 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81151) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81151) (weight := fun _ => 1) (xs := [256, 277, 320, 341, 1023]) check rows elimOK (by decide) (by decide) cover81151 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover81260 : P.CoversSplit 26 10 81260 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h81260 : P.leaf 36 81260 = 176376 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81260) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81260) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover81260 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover81261 : P.CoversSplit 26 10 81261 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h81261 : P.leaf 36 81261 = 180274 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81261) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81261) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover81261 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover81262 : P.CoversSplit 26 10 81262 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h81262 : P.leaf 36 81262 = 877236 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81262) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81262) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover81262 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover81263 : P.CoversSplit 26 10 81263 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h81263 : P.leaf 36 81263 = 910198 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81263) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81263) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover81263 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover81278 : P.CoversSplit 26 10 81278 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h81278 : P.leaf 36 81278 = 3413757 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81278) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81278) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover81278 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover81279 : P.CoversSplit 26 10 81279 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h81279 : P.leaf 36 81279 = 3791700 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81279) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81279) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover81279 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover81335 : P.CoversSplit 26 10 81335 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000200000000001000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 538, 629, 636, 930, 972, 1315, 1658]) (by decide +kernel)

theorem h81335 : P.leaf 36 81335 = 3173551 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 81335) (keep := keep9) (twice := twice9) rows (by decide) (by decide) bal9 (invRow9 (H := 81335) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81335) (weight := rowWeight keep9 twice9) (xs := [256, 276, 321, 341, 1023]) check rows elimOK (by decide) (by decide) cover81335 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover81336 : P.CoversSplit 26 10 81336 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 481, 482, 531, 629, 636, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h81336 : P.leaf 36 81336 = 44100 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81336) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81336) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover81336 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover81337 : P.CoversSplit 26 10 81337 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 481, 482, 531, 629, 636, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h81337 : P.leaf 36 81337 = 1577976 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81337) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81337) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover81337 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover81339 : P.CoversSplit 26 10 81339 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 481, 482, 531, 629, 636, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h81339 : P.leaf 36 81339 = 3449824 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81339) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81339) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover81339 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover81340 : P.CoversSplit 26 10 81340 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 629, 636, 930, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h81340 : P.leaf 36 81340 = 1126320 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81340) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81340) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover81340 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover81341 : P.CoversSplit 26 10 81341 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 629, 636, 930, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h81341 : P.leaf 36 81341 = 2555700 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81341) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81341) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover81341 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover81343 : P.CoversSplit 26 10 81343 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 629, 636, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h81343 : P.leaf 36 81343 = 5305160 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81343) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81343) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover81343 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover81353 : P.CoversSplit 26 10 81353 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 481, 482, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h81353 : P.leaf 36 81353 = 100096 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81353) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81353) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover81353 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover81355 : P.CoversSplit 26 10 81355 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 481, 482, 530, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h81355 : P.leaf 36 81355 = 690848 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81355) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81355) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover81355 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover81356 : P.CoversSplit 26 10 81356 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h81356 : P.leaf 36 81356 = 103584 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81356) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81356) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover81356 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover81357 : P.CoversSplit 26 10 81357 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h81357 : P.leaf 36 81357 = 954792 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81357) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81357) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover81357 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover81358 : P.CoversSplit 26 10 81358 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h81358 : P.leaf 36 81358 = 257136 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81358) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81358) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover81358 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover81359 : P.CoversSplit 26 10 81359 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h81359 : P.leaf 36 81359 = 2337492 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81359) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81359) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover81359 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover81371 : P.CoversSplit 26 10 81371 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 481, 482, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h81371 : P.leaf 36 81371 = 2984152 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81371) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81371) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover81371 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover81372 : P.CoversSplit 26 10 81372 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h81372 : P.leaf 36 81372 = 2038468 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81372) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81372) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover81372 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover81373 : P.CoversSplit 26 10 81373 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h81373 : P.leaf 36 81373 = 2587148 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81373) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81373) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover81373 (by decide) (by decide) (by decide +kernel)
  decide +kernel

def seg : List (ℕ × ℕ) := [(79838, 720), (79839, 720), (79852, 360), (79853, 360), (79854, 720), (79855, 720), (79870, 360), (79871, 360), (81150, 60), (81151, 60), (81260, 360), (81261, 360), (81262, 720), (81263, 720), (81278, 360), (81279, 360), (81335, 90), (81336, 360), (81337, 720), (81339, 360), (81340, 360), (81341, 720), (81343, 360), (81353, 180), (81355, 360), (81356, 720), (81357, 720), (81358, 720), (81359, 720), (81371, 180), (81372, 720), (81373, 720)]

theorem segOK : checkSeg 20 perms 79838 81374 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 79838 81374 15330 1959390318390 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1959390318390)
    (SegSum.cons (w := 720) h79838 (SegSum.cons (w := 720) h79839 (SegSum.cons (w := 360) h79852 (SegSum.cons (w := 360) h79853 (SegSum.cons (w := 720) h79854 (SegSum.cons (w := 720) h79855 (SegSum.cons (w := 360) h79870 (SegSum.cons (w := 360) h79871 (SegSum.cons (w := 60) h81150 (SegSum.cons (w := 60) h81151 (SegSum.cons (w := 360) h81260 (SegSum.cons (w := 360) h81261 (SegSum.cons (w := 720) h81262 (SegSum.cons (w := 720) h81263 (SegSum.cons (w := 360) h81278 (SegSum.cons (w := 360) h81279 (SegSum.cons (w := 90) h81335 (SegSum.cons (w := 360) h81336 (SegSum.cons (w := 720) h81337 (SegSum.cons (w := 360) h81339 (SegSum.cons (w := 360) h81340 (SegSum.cons (w := 720) h81341 (SegSum.cons (w := 360) h81343 (SegSum.cons (w := 180) h81353 (SegSum.cons (w := 360) h81355 (SegSum.cons (w := 720) h81356 (SegSum.cons (w := 720) h81357 (SegSum.cons (w := 720) h81358 (SegSum.cons (w := 720) h81359 (SegSum.cons (w := 180) h81371 (SegSum.cons (w := 720) h81372 (SegSum.cons (w := 720) h81373 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S49
