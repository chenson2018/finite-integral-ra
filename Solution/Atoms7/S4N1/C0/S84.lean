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

namespace RACert.S4N1.C0.S84

open RACert RACert.Problem

theorem cover59132 : P.CoversSplit 24 10 59132 0xfcfcfcfcf8f8a8a8fcfcfcfcf8f8a8a8fcfcfcfcf800a800fcfcfcfcf800a800fcccfcccf8c8a888cc00cc00c8008800fcccfcccf800a800cc00cc00c8008800fcfcfcfcf8f8a8a8fcfcfcfcf8f8a8a8fcfcfcfcf800a800fcfcfcfcf800a800f0c0f0c0f0c0a080c000c000c0008000f0c0f0c000000000c000c00000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 872, 1202, 1308, 1601]) (by decide +kernel)

theorem c59132_0 : P.sumLeaves 24 60551168 370 = 20708630 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 59132) (lo := 0) (len := 370) (W := 20708630) check rows elimOK (by decide) (by decide) cover59132 (by decide)
  decide +kernel

theorem c59132_1 : P.sumLeaves 24 60551538 173 = 48557530 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 59132) (lo := 370) (len := 173) (W := 48557530) check rows elimOK (by decide) (by decide) cover59132 (by decide)
  decide +kernel

theorem c59132_2 : P.sumLeaves 24 60551711 264 = 54140882 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 59132) (lo := 543) (len := 264) (W := 54140882) check rows elimOK (by decide) (by decide) cover59132 (by decide)
  decide +kernel

theorem c59132_3 : P.sumLeaves 24 60551975 168 = 93575137 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 59132) (lo := 807) (len := 168) (W := 93575137) check rows elimOK (by decide) (by decide) cover59132 (by decide)
  decide +kernel

theorem c59132_4 : P.sumLeaves 24 60552143 49 = 51519908 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 59132) (lo := 975) (len := 49) (W := 51519908) check rows elimOK (by decide) (by decide) cover59132 (by decide)
  decide +kernel

theorem h59132 : P.leaf 34 59132 = 268502087 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(370, 20708630), (173, 48557530), (264, 54140882), (168, 93575137), (49, 51519908)]) (.cons c59132_0 (.cons c59132_1 (.cons c59132_2 (.cons c59132_3 (.cons c59132_4 (.nil)))))) (by decide) (by decide))

theorem h28094 : P.leaf 34 28094 = 268502087 :=
  orient5 (v := 59132) (by decide) (by decide +kernel) h59132

theorem cover28095 : P.CoversSplit 24 10 28095 0xfffffffffafaf0f0fffffffffafaf0f0fffffffffafaf0f0ffff000000000000ffccffccfac8f0c0ccccccccc8c8c0c0ffccffccfac8f0c0cccc000000000000fffffffffafaf0f0fffffffffafaf0f0fffffffffafaf0f0ffff000000000000ffccffccfac8f0c0ccccccccc8c8c0c0ffccffccf000f000cccc000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 858, 865, 1202, 1251, 1259, 1601]) (ps := [(8, [1217, 1609], [1272])]) (by decide +kernel)

theorem c28095_0 : P.sumLeaves 24 28769280 247 = 33040498 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28095) (lo := 0) (len := 247) (W := 33040498) check rows elimOK (by decide) (by decide) cover28095 (by decide)
  decide +kernel

theorem c28095_1 : P.sumLeaves 24 28769527 168 = 45705885 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28095) (lo := 247) (len := 168) (W := 45705885) check rows elimOK (by decide) (by decide) cover28095 (by decide)
  decide +kernel

theorem c28095_2 : P.sumLeaves 24 28769695 174 = 101226563 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28095) (lo := 415) (len := 174) (W := 101226563) check rows elimOK (by decide) (by decide) cover28095 (by decide)
  decide +kernel

theorem c28095_3 : P.sumLeaves 24 28769869 174 = 107798844 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28095) (lo := 589) (len := 174) (W := 107798844) check rows elimOK (by decide) (by decide) cover28095 (by decide)
  decide +kernel

theorem c28095_4 : P.sumLeaves 24 28770043 168 = 111945972 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28095) (lo := 763) (len := 168) (W := 111945972) check rows elimOK (by decide) (by decide) cover28095 (by decide)
  decide +kernel

theorem c28095_5 : P.sumLeaves 24 28770211 93 = 176732630 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28095) (lo := 931) (len := 93) (W := 176732630) check rows elimOK (by decide) (by decide) cover28095 (by decide)
  decide +kernel

theorem h28095 : P.leaf 34 28095 = 576450392 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(247, 33040498), (168, 45705885), (174, 101226563), (174, 107798844), (168, 111945972), (93, 176732630)]) (.cons c28095_0 (.cons c28095_1 (.cons c28095_2 (.cons c28095_3 (.cons c28095_4 (.cons c28095_5 (.nil))))))) (by decide) (by decide))

theorem cover58860 : P.CoversSplit 24 10 58860 0xffffffffeae0a0a0ffffffffeae0a0a0f000f50000000000f000f50000000000eec0eec0eac0a080cc00cc00c8008000e000e40000000000c000c40000000000f000f000e000a000f030f030e020a020f000f00000000000f000f001000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 858, 860, 865, 872, 915]) (by decide +kernel)

noncomputable def f58860 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (60272640 + i)

theorem c58860_0 : rowSum f58860 0 955 = 15633680 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 58860) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover58860 (by decide)
  decide +kernel

theorem c58860_1 : rowSum f58860 955 69 = 6617240 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 58860) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover58860 (by decide)
  decide +kernel

theorem sum58860 : rowSum f58860 0 1024 = 22250920 :=
  rowSum_append (F := f58860) (lo := 0) (n := 955) (m := 69) (A := 15633680) (B := 6617240) c58860_0 (c58860_1)

theorem h58860 : P.leaf 34 58860 = 22250920 :=
  leaf_weighted (k := 24) (d := 10) (H := 58860) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 58860) (by decide) (by decide +kernel)) sum58860

theorem h28140 : P.leaf 34 28140 = 22250920 :=
  orient24 (v := 58860) (by decide) (by decide +kernel) h58860

theorem cover28141 : P.CoversSplit 24 10 28141 0xff00ff00ea00a0000000000000000000ff000000000000000000000000000000ff00ff00ea00a0000000000000000000ff000000000000000000000000000000ff00ff00ea00a0000000000000000000ff0005000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 858, 865, 915, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c28141_0 : P.sumLeaves 24 28816384 1024 = 39180926 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28141) (lo := 0) (len := 1024) (W := 39180926) check rows elimOK (by decide) (by decide) cover28141 (by decide)
  decide +kernel

theorem h28141 : P.leaf 34 28141 = 39180926 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 39180926)]) (.cons c28141_0 (.nil)) (by decide) (by decide))

theorem cover28142 : P.CoversSplit 24 10 28142 0xff00ff00fa00fa000000000000000000ff000000000000000000000000000000ee0cee0cea08ea08ccccccccc8c8c8c8ee0c000000000000cccc000000000000ff00ff00fa00fa000000000000000000ff0005000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 522, 858, 865, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c28142_0 : P.sumLeaves 24 28817408 745 = 22804085 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28142) (lo := 0) (len := 745) (W := 22804085) check rows elimOK (by decide) (by decide) cover28142 (by decide)
  decide +kernel

theorem c28142_1 : P.sumLeaves 24 28818153 279 = 48318361 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28142) (lo := 745) (len := 279) (W := 48318361) check rows elimOK (by decide) (by decide) cover28142 (by decide)
  decide +kernel

theorem h28142 : P.leaf 34 28142 = 71122446 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(745, 22804085), (279, 48318361)]) (.cons c28142_0 (.cons c28142_1 (.nil))) (by decide) (by decide))

theorem cover28143 : P.CoversSplit 24 10 28143 0xff00ff00fa00fa000000000000000000ff000000000000000000000000000000ff00ff00fa00fa000000000000000000ff000000000000000000000000000000ff00ff00fa00fa000000000000000000ff0005000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 858, 865, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c28143_0 : P.sumLeaves 24 28818432 1002 = 89480455 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28143) (lo := 0) (len := 1002) (W := 89480455) check rows elimOK (by decide) (by decide) cover28143 (by decide)
  decide +kernel

theorem c28143_1 : P.sumLeaves 24 28819434 22 = 34564722 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28143) (lo := 1002) (len := 22) (W := 34564722) check rows elimOK (by decide) (by decide) cover28143 (by decide)
  decide +kernel

theorem h28143 : P.leaf 34 28143 = 124045177 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1002, 89480455), (22, 34564722)]) (.cons c28143_0 (.cons c28143_1 (.nil))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(28094, 48), (28095, 48), (28140, 24), (28141, 24), (28142, 48), (28143, 48)]

theorem segOK : checkSeg 16 perms 28094 28158 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 28094 28158 240 51400129200 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 51400129200)
    (SegSum.cons (w := 48) h28094 (SegSum.cons (w := 48) h28095 (SegSum.cons (w := 24) h28140 (SegSum.cons (w := 24) h28141 (SegSum.cons (w := 48) h28142 (SegSum.cons (w := 48) h28143 (show SegSum (P.leaf 34) [] 0 from rfl))))))) (by decide)

end RACert.S4N1.C0.S84
