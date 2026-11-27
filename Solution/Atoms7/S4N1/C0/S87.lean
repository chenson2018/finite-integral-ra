/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S4N1.C0.Actions

/-! Generated identity-class certificate for the product-row count. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S4N1.C0.S87

open RACert RACert.Problem

theorem cover23998 : P.CoversSplit 24 10 23998 0xfffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0ffff000000000000ccc0ccc088808080cc00cc0088008000ccc0ccc088808080cc00000000000000fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0ffff000000000000ccc0ccc088808080cc00cc008800800000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 858, 865, 1202, 1210, 1251, 1259, 1308, 1601]) (by decide +kernel)

theorem c23998_0 : P.sumLeaves 24 24573952 401 = 15573166 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23998) (lo := 0) (len := 401) (W := 15573166) check rows elimOK (by decide) (by decide) cover23998 (by decide)
  decide +kernel

theorem c23998_1 : P.sumLeaves 24 24574353 182 = 37662825 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23998) (lo := 401) (len := 182) (W := 37662825) check rows elimOK (by decide) (by decide) cover23998 (by decide)
  decide +kernel

theorem c23998_2 : P.sumLeaves 24 24574535 300 = 45812312 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23998) (lo := 583) (len := 300) (W := 45812312) check rows elimOK (by decide) (by decide) cover23998 (by decide)
  decide +kernel

theorem c23998_3 : P.sumLeaves 24 24574835 128 = 93068206 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23998) (lo := 883) (len := 128) (W := 93068206) check rows elimOK (by decide) (by decide) cover23998 (by decide)
  decide +kernel

theorem c23998_4 : P.sumLeaves 24 24574963 13 = 23469660 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23998) (lo := 1011) (len := 13) (W := 23469660) check rows elimOK (by decide) (by decide) cover23998 (by decide)
  decide +kernel

theorem h23998 : P.leaf 34 23998 = 215586169 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(401, 15573166), (182, 37662825), (300, 45812312), (128, 93068206), (13, 23469660)]) (.cons c23998_0 (.cons c23998_1 (.cons c23998_2 (.cons c23998_3 (.cons c23998_4 (.nil)))))) (by decide) (by decide))

theorem cover23999 : P.CoversSplit 24 10 23999 0xfffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0ffff000000000000cccccccc88888080cccccccc88888080cccccccc88888080cccc000000000000fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0ffff000000000000cccccccc88888080cccccccc8888808000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 858, 865, 1202, 1210, 1251, 1259, 1308, 1601]) (by decide +kernel)

theorem c23999_0 : P.sumLeaves 24 24574976 372 = 27222395 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23999) (lo := 0) (len := 372) (W := 27222395) check rows elimOK (by decide) (by decide) cover23999 (by decide)
  decide +kernel

theorem c23999_1 : P.sumLeaves 24 24575348 128 = 66165214 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23999) (lo := 372) (len := 128) (W := 66165214) check rows elimOK (by decide) (by decide) cover23999 (by decide)
  decide +kernel

theorem c23999_2 : P.sumLeaves 24 24575476 326 = 73433151 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23999) (lo := 500) (len := 326) (W := 73433151) check rows elimOK (by decide) (by decide) cover23999 (by decide)
  decide +kernel

theorem c23999_3 : P.sumLeaves 24 24575802 128 = 106895247 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23999) (lo := 826) (len := 128) (W := 106895247) check rows elimOK (by decide) (by decide) cover23999 (by decide)
  decide +kernel

theorem c23999_4 : P.sumLeaves 24 24575930 70 = 143460204 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23999) (lo := 954) (len := 70) (W := 143460204) check rows elimOK (by decide) (by decide) cover23999 (by decide)
  decide +kernel

theorem h23999 : P.leaf 34 23999 = 417176211 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(372, 27222395), (128, 66165214), (326, 73433151), (128, 106895247), (70, 143460204)]) (.cons c23999_0 (.cons c23999_1 (.cons c23999_2 (.cons c23999_3 (.cons c23999_4 (.nil)))))) (by decide) (by decide))

theorem cover24008 : P.CoversSplit 24 10 24008 0xffffffffe0e0a0a0ffffffffe0e0a0a0aaaa000000000000aaaa000000000000ccc0ccc080008000cc00cc008000800088800000000000008800000000000000ff00ff00e000a0000000000000000000aa0055000000000000aa0055000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 516, 522, 858, 865, 916, 1202, 1210, 1259, 1601]) (by decide +kernel)

noncomputable def f24008 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (24584192 + i)

theorem c24008_0 : rowSum f24008 0 1024 = 3867723 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 24008) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover24008 (by decide)
  decide +kernel

theorem sum24008 : rowSum f24008 0 1024 = 3867723 :=
  c24008_0

theorem h24008 : P.leaf 34 24008 = 3867723 :=
  leaf_weighted (k := 24) (d := 10) (H := 24008) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 24008) (by decide) (by decide +kernel)) sum24008

theorem cover24009 : P.CoversSplit 24 10 24009 0xffffffffe0e00000ffffffffe0e00000ffff000000000000ffff000000000000cccccccc80000000cc00cc0080000000cccc000040000000cc00000000000000ff00ff00e00000000000000000000000ff0000000000000000ff000000000000000000000000000000cc008800800000000000000000000000cc000000400000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 522, 858, 865, 916, 1202, 1210, 1259, 1601]) (ps := [(11, [858, 879], [472]), (17, [536], [1251]), (18, [1210], [1264])]) (by decide +kernel)

theorem contract24009_0 : P.leaf 30 384144 = 13152 := by
  exact leaf_contract_factors (k := 30) (b := 16) (H := 384144) (ss := [(30, 11, 472), (7, 1, 523), (17, 3, 536), (8, 3, 565), (11, 1, 879), (18, 1, 921), (29, 0, 1259), (2, 1, 473), (3, 1, 418), (27, 1, 473), (31, 1, 1251), (21, 0, 1266), (14, 1, 972), (20, 1, 1272)]) (ids := [2, 3, 4, 8, 10, 11, 13, 17, 20, 21, 22, 23, 24, 26, 7, 14]) (cs := [1, 1, 2, 3, 4, 1, 1, 16, 5, 1, 6, 7, 1, 8, 17, 1, 1, 9, 1, 0, 10, 11, 12, 13, 14, 1, 15, 0, 1, 1]) (bs := [14, 2]) (W := 13152) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c24009_0 : P.sumLeaves 24 24585216 64 = 13152 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 384144) rows (by decide) (by decide)).symm.trans contract24009_0

theorem c24009_1 : P.sumLeaves 24 24585280 192 = 69285 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24009) (lo := 64) (len := 192) (W := 69285) check rows elimOK (by decide) (by decide) cover24009 (by decide)
  decide +kernel

theorem contract24009_2 : P.leaf 30 384148 = 768 := by
  exact leaf_contract_factors (k := 30) (b := 12) (H := 384148) (ss := [(30, 11, 472), (7, 1, 523), (17, 3, 536), (8, 3, 565), (11, 1, 879), (31, 1, 1210), (3, 0, 1259), (5, 1, 417), (2, 0, 418), (14, 0, 411), (15, 0, 411), (18, 1, 475), (20, 1, 482), (21, 0, 488), (29, 0, 558), (12, 1, 818), (13, 1, 971), (16, 1, 1314)]) (ids := [2, 7, 17, 20, 23, 25, 8, 21, 22, 26, 4, 24]) (cs := [0, 0, 2, 1, 12, 1, 0, 3, 8, 1, 1, 1, 0, 0, 1, 0, 1, 4, 1, 0, 5, 9, 10, 6, 13, 7, 11, 0, 1, 1]) (bs := [6, 4, 2]) (W := 768) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c24009_2 : P.sumLeaves 24 24585472 64 = 768 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 384148) rows (by decide) (by decide)).symm.trans contract24009_2

theorem c24009_3 : P.sumLeaves 24 24585536 192 = 550332 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24009) (lo := 320) (len := 192) (W := 550332) check rows elimOK (by decide) (by decide) cover24009 (by decide)
  decide +kernel

theorem contract24009_4 : P.leaf 30 384152 = 76544 := by
  exact leaf_contract_factors (k := 30) (b := 18) (H := 384152) (ss := [(30, 11, 472), (7, 1, 523), (17, 1, 536), (8, 1, 565), (11, 1, 879), (12, 1, 916), (29, 1, 916), (18, 1, 921), (31, 1, 1251), (21, 1, 1266), (20, 1, 1272), (27, 1, 1601)]) (ids := [0, 1, 2, 3, 4, 8, 11, 12, 13, 14, 20, 21, 22, 23, 26, 7, 17, 24]) (cs := [2, 3, 4, 5, 6, 1, 1, 17, 7, 1, 1, 8, 9, 10, 11, 1, 1, 18, 1, 1, 12, 13, 14, 15, 19, 1, 16, 1, 1, 1]) (bs := [15, 3]) (W := 76544) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c24009_4 : P.sumLeaves 24 24585728 64 = 76544 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 384152) rows (by decide) (by decide)).symm.trans contract24009_4

theorem c24009_5 : P.sumLeaves 24 24585792 375 = 3929082 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24009) (lo := 576) (len := 375) (W := 3929082) check rows elimOK (by decide) (by decide) cover24009 (by decide)
  decide +kernel

theorem c24009_6 : P.sumLeaves 24 24586167 73 = 4398740 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24009) (lo := 951) (len := 73) (W := 4398740) check rows elimOK (by decide) (by decide) cover24009 (by decide)
  decide +kernel

theorem h24009 : P.leaf 34 24009 = 9037903 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 13152), (192, 69285), (64, 768), (192, 550332), (64, 76544), (375, 3929082), (73, 4398740)]) (.cons c24009_0 (.cons c24009_1 (.cons c24009_2 (.cons c24009_3 (.cons c24009_4 (.cons c24009_5 (.cons c24009_6 (.nil)))))))) (by decide) (by decide))

theorem cover24011 : P.CoversSplit 24 10 24011 0xfffffffff0f0a0a0fffffffff0f0a0a0ffff000000000000ffff000000000000cccccccc80008000cc00cc0080008000cccc000040000000cc00000040000000fffffffff0f0a0a00000000000000000ffff55550000000000ff0000000000000000000000800080000000000000000000000000004000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 516, 522, 858, 865, 916, 1202, 1210, 1259, 1601]) (ps := [(3, [536], [472])]) (by decide +kernel)

noncomputable def f24011 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (24587264 + i)

theorem c24011_0 : rowSum f24011 0 933 = 11435850 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 24011) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover24011 (by decide)
  decide +kernel

theorem c24011_1 : rowSum f24011 933 91 = 10631712 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 24011) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover24011 (by decide)
  decide +kernel

theorem sum24011 : rowSum f24011 0 1024 = 22067562 :=
  rowSum_append (F := f24011) (lo := 0) (n := 933) (m := 91) (A := 11435850) (B := 10631712) c24011_0 (c24011_1)

theorem h24011 : P.leaf 34 24011 = 22067562 :=
  leaf_weighted (k := 24) (d := 10) (H := 24011) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 24011) (by decide) (by decide +kernel)) sum24011

theorem cover24012 : P.CoversSplit 24 10 24012 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [472]) (by decide +kernel)

theorem c24012_0 : P.sumLeaves 24 24588288 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24012) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover24012 (by decide)
  decide +kernel

theorem h24012 : P.leaf 34 24012 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c24012_0 (.nil)) (by decide) (by decide))

theorem cover24013 : P.CoversSplit 24 10 24013 0xffffffffe0e0a0a0ffffffffe0e0a0a0ffff000000000000ffff000000000000cccccccc80008000cc00cc0080008000cccc000040000000cc00000000000000ff00ff00e000a0000000000000000000ff0055000000000000330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 522, 858, 865, 916, 1202, 1210, 1259, 1601]) (ps := [(14, [867], [916]), (17, [536], [1251])]) (by decide +kernel)

theorem c24013_0 : P.sumLeaves 24 24589312 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24013) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover24013 (by decide)
  decide +kernel

theorem contract24013_1 : P.leaf 30 384212 = 0 := by
  exact leaf_contract_zero (ss := [(11, 1, 472), (7, 1, 523), (17, 3, 536), (8, 3, 565), (3, 0, 1259), (5, 1, 417), (2, 1, 418), (30, 18, 524), (29, 0, 1259), (14, 0, 916), (20, 1, 531), (21, 1, 537), (9, 1, 629), (12, 1, 818), (18, 1, 867), (15, 0, 916), (4, 1, 487), (27, 0, 916), (13, 1, 971)]) (q := 972) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c24013_1 : P.sumLeaves 24 24589568 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 384212) rows (by decide) (by decide)).symm.trans contract24013_1

theorem c24013_2 : P.sumLeaves 24 24589632 192 = 2203382 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24013) (lo := 320) (len := 192) (W := 2203382) check rows elimOK (by decide) (by decide) cover24013 (by decide)
  decide +kernel

theorem contract24013_3 : P.leaf 30 384216 = 109952 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 384216) (ss := [(11, 1, 472), (7, 1, 523), (17, 1, 536), (8, 1, 565), (18, 1, 921), (30, 1, 1251), (31, 1, 1251), (29, 1, 1259), (21, 1, 1266), (20, 1, 1272), (27, 1, 1601)]) (ids := [0, 1, 2, 3, 4, 8, 10, 11, 12, 13, 14, 20, 21, 22, 24, 26, 7, 17, 23]) (cs := [2, 3, 4, 5, 6, 1, 1, 18, 7, 1, 8, 9, 10, 11, 12, 1, 1, 19, 1, 1, 13, 14, 15, 20, 16, 1, 17, 1, 1, 1]) (bs := [16, 3]) (W := 109952) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c24013_3 : P.sumLeaves 24 24589824 64 = 109952 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 384216) rows (by decide) (by decide)).symm.trans contract24013_3

theorem c24013_4 : P.sumLeaves 24 24589888 369 = 10280304 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24013) (lo := 576) (len := 369) (W := 10280304) check rows elimOK (by decide) (by decide) cover24013 (by decide)
  decide +kernel

theorem c24013_5 : P.sumLeaves 24 24590257 79 = 13965676 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24013) (lo := 945) (len := 79) (W := 13965676) check rows elimOK (by decide) (by decide) cover24013 (by decide)
  decide +kernel

theorem h24013 : P.leaf 34 24013 = 26559314 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 0), (192, 2203382), (64, 109952), (369, 10280304), (79, 13965676)]) (.cons c24013_0 (.cons c24013_1 (.cons c24013_2 (.cons c24013_3 (.cons c24013_4 (.cons c24013_5 (.nil))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(23998, 48), (23999, 48), (24008, 6), (24009, 24), (24011, 24), (24012, 24), (24013, 48)]

theorem segOK : checkSeg 16 perms 23998 24015 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 23998 24015 222 32417178810 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 32417178810)
    (SegSum.cons (w := 48) h23998 (SegSum.cons (w := 48) h23999 (SegSum.cons (w := 6) h24008 (SegSum.cons (w := 24) h24009 (SegSum.cons (w := 24) h24011 (SegSum.cons (w := 24) h24012 (SegSum.cons (w := 48) h24013 (show SegSum (P.leaf 34) [] 0 from rfl)))))))) (by decide)

end RACert.S4N1.C0.S87
