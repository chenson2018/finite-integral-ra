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

namespace RACert.S4N1.C0.S73

open RACert RACert.Problem

theorem cover24038 : P.CoversSplit 24 10 24038 0xfffffffffafaaaaa0000000000000000ffff0000000050500000000000000000ccc0ccc0888088800000000000000000ccc00000404040400000000000000000fffffffffafaaaaa0000000000000000ffff00000000505000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 466, 515, 522, 858, 865, 1202, 1210, 1259, 1601]) (ps := [(18, [879], [1210])]) (by decide +kernel)

theorem c24038_0 : P.sumLeaves 24 24614912 762 = 15044458 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24038) (lo := 0) (len := 762) (W := 15044458) check rows elimOK (by decide) (by decide) cover24038 (by decide)
  decide +kernel

theorem c24038_1 : P.sumLeaves 24 24615674 262 = 41384452 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24038) (lo := 762) (len := 262) (W := 41384452) check rows elimOK (by decide) (by decide) cover24038 (by decide)
  decide +kernel

theorem h24038 : P.leaf 34 24038 = 56428910 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(762, 15044458), (262, 41384452)]) (.cons c24038_0 (.cons c24038_1 (.nil))) (by decide) (by decide))

theorem h23996 : P.leaf 34 23996 = 56428910 :=
  orient4 (v := 24038) (by decide) (by decide +kernel) h24038

theorem cover24039 : P.CoversSplit 24 10 24039 0xfffffffffafaaaaaffff0000fafa0000ffff000000005050ffff000000000000cccccccc88888888cccc000088880000cccc000040404040cccc000040400000fffffffffafaaaaa0000000000000000ffff55550000505000330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [466, 515, 522, 858, 865, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c24039_0 : P.sumLeaves 24 24615936 598 = 24755643 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24039) (lo := 0) (len := 598) (W := 24755643) check rows elimOK (by decide) (by decide) cover24039 (by decide)
  decide +kernel

theorem c24039_1 : P.sumLeaves 24 24616534 348 = 45162767 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24039) (lo := 598) (len := 348) (W := 45162767) check rows elimOK (by decide) (by decide) cover24039 (by decide)
  decide +kernel

theorem c24039_2 : P.sumLeaves 24 24616882 78 = 59976886 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24039) (lo := 946) (len := 78) (W := 59976886) check rows elimOK (by decide) (by decide) cover24039 (by decide)
  decide +kernel

theorem h24039 : P.leaf 34 24039 = 129895296 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(598, 24755643), (348, 45162767), (78, 59976886)]) (.cons c24039_0 (.cons c24039_1 (.cons c24039_2 (.nil)))) (by decide) (by decide))

theorem h23997 : P.leaf 34 23997 = 129895296 :=
  orient4 (v := 24039) (by decide) (by decide +kernel) h24039

theorem cover59260 : P.CoversSplit 24 10 59260 0xfcfcfcfcf8f8a8a8fcfcfcfcf8f8a8a8fcfcfcfcf800a800fcfcfcfcf800a800fcccfcccf8c8a8880000000000000000fcccfcccf800a8000000000000000000fcfcfcfcf8f8a8a8fcfcfcfcf8f8a8a8fcfcfcfcf800a800fcfcfcfcf800a800f0c0f0c0f0c0a0800000000000000000f0c0f0c0000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 466, 473, 872, 1202, 1308, 1601]) (by decide +kernel)

theorem c59260_0 : P.sumLeaves 24 60682240 383 = 12489794 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 59260) (lo := 0) (len := 383) (W := 12489794) check rows elimOK (by decide) (by decide) cover59260 (by decide)
  decide +kernel

theorem c59260_1 : P.sumLeaves 24 60682623 238 = 41723181 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 59260) (lo := 383) (len := 238) (W := 41723181) check rows elimOK (by decide) (by decide) cover59260 (by decide)
  decide +kernel

theorem c59260_2 : P.sumLeaves 24 60682861 257 = 48191676 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 59260) (lo := 621) (len := 257) (W := 48191676) check rows elimOK (by decide) (by decide) cover59260 (by decide)
  decide +kernel

theorem c59260_3 : P.sumLeaves 24 60683118 146 = 113181518 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 59260) (lo := 878) (len := 146) (W := 113181518) check rows elimOK (by decide) (by decide) cover59260 (by decide)
  decide +kernel

theorem h59260 : P.leaf 34 59260 = 215586169 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(383, 12489794), (238, 41723181), (257, 48191676), (146, 113181518)]) (.cons c59260_0 (.cons c59260_1 (.cons c59260_2 (.cons c59260_3 (.nil))))) (by decide) (by decide))

theorem h23998 : P.leaf 34 23998 = 215586169 :=
  orient5 (v := 59260) (by decide) (by decide +kernel) h59260

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
  leaf_weighted (k := 24) (d := 10) (H := 24008) (keep := keep5) (twice := twice5) rows (by decide) (by decide) (bal5) (invRow5 (H := 24008) (by decide) (by decide +kernel)) sum24008

theorem cover59740 : P.CoversSplit 24 10 59740 0xf00ff00ff0000000f00ff00ff0000000f000f00040000000f000f00040000000f000f000f00000000000000000000000f000f000400000000000000000000000f000f000f0000000f000f000f0000000f000f00050000000f000f000500000002000200020000000000000000000000030003000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 858, 859, 865, 866, 908, 915, 1202, 1308, 1601]) (ps := [(8, [537, 586], [523, 565])]) (by decide +kernel)

noncomputable def f59740 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (61173760 + i)

theorem c59740_0 : rowSum f59740 0 1024 = 9037903 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59740) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover59740 (by decide)
  decide +kernel

theorem sum59740 : rowSum f59740 0 1024 = 9037903 :=
  c59740_0

theorem h59740 : P.leaf 34 59740 = 9037903 :=
  leaf_weighted (k := 24) (d := 10) (H := 59740) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 59740) (by decide) (by decide +kernel)) sum59740

theorem h24009 : P.leaf 34 24009 = 9037903 :=
  orient24 (v := 59740) (by decide) (by decide +kernel) h59740

def seg : List (ℕ × ℕ) := [(23996, 48), (23997, 48), (23998, 48), (23999, 48), (24008, 6), (24009, 24)]

theorem segOK : checkSeg 16 perms 23996 24011 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 23996 24011 222 39556272138 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 39556272138)
    (SegSum.cons (w := 48) h23996 (SegSum.cons (w := 48) h23997 (SegSum.cons (w := 48) h23998 (SegSum.cons (w := 48) h23999 (SegSum.cons (w := 6) h24008 (SegSum.cons (w := 24) h24009 (show SegSum (P.leaf 34) [] 0 from rfl))))))) (by decide)

end RACert.S4N1.C0.S73
