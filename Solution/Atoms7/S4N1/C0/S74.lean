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

namespace RACert.S4N1.C0.S74

open RACert RACert.Problem

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
  leaf_weighted (k := 24) (d := 10) (H := 24011) (keep := keep5) (twice := twice5) rows (by decide) (by decide) (bal5) (invRow5 (H := 24011) (by decide) (by decide +kernel)) sum24011

theorem cover24012 : P.CoversSplit 24 10 24012 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [472]) (by decide +kernel)

theorem h24012 : P.leaf 34 24012 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 24012) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 24012) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover24012 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover24041 : P.CoversSplit 24 10 24041 0xffff0000eae00000ffff0000eae00000ffff000000000000ffff000000000000cccc000088800000cc00000088000000cccc000040400000cc00000040000000ff000000ea0000000000000000000000ff0000000000000000330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [472, 473, 515, 522, 858, 865, 916, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c24041_0 : P.sumLeaves 24 24617984 927 = 12590450 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24041) (lo := 0) (len := 927) (W := 12590450) check rows elimOK (by decide) (by decide) cover24041 (by decide)
  decide +kernel

theorem c24041_1 : P.sumLeaves 24 24618911 97 = 13968864 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24041) (lo := 927) (len := 97) (W := 13968864) check rows elimOK (by decide) (by decide) cover24041 (by decide)
  decide +kernel

theorem h24041 : P.leaf 34 24041 = 26559314 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(927, 12590450), (97, 13968864)]) (.cons c24041_0 (.cons c24041_1 (.nil))) (by decide) (by decide))

theorem h24013 : P.leaf 34 24013 = 26559314 :=
  orient4 (v := 24041) (by decide) (by decide +kernel) h24041

theorem cover24015 : P.CoversSplit 24 10 24015 0xfffffffff0f0a0a0fffffffff0f0a0a0ffff000000005050ffff000000005000cccccccc80008000cc00cc0080008000cccc000040004000cc00000040004000fffffffff0f0a0a00000000000000000ffff55550000505000ff005500000050000000000080008000cc008800800080000000000040004000cc004400400040 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 858, 865, 1202, 1210, 1259, 1601]) (ps := [(17, [1259], [1251]), (18, [1210], [1264])]) (by decide +kernel)

noncomputable def f24015 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (24591360 + i)

theorem c24015_0 : rowSum f24015 0 739 = 24414652 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 24015) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover24015 (by decide)
  decide +kernel

theorem c24015_1 : rowSum f24015 739 285 = 40291821 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 24015) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover24015 (by decide)
  decide +kernel

theorem sum24015 : rowSum f24015 0 1024 = 64706473 :=
  rowSum_append (F := f24015) (lo := 0) (n := 739) (m := 285) (A := 24414652) (B := 40291821) c24015_0 (c24015_1)

theorem h24015 : P.leaf 34 24015 = 64706473 :=
  leaf_weighted (k := 24) (d := 10) (H := 24015) (keep := keep5) (twice := twice5) rows (by decide) (by decide) (bal5) (invRow5 (H := 24015) (by decide) (by decide +kernel)) sum24015

theorem cover59727 : P.CoversSplit 24 10 59727 0xfffffffffafa0000fffffffffafa0000a5a5a5a504000000a5a5a5a504000000ffccffccfac800000000000000000000a584a584040000000000000000000000cc33cc33c8320000cc33cc33c8320000842184210000000084218421000000000020002000200000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 516, 522, 572, 858, 859, 865, 915, 1202, 1217, 1601, 1609]) (by decide +kernel)

noncomputable def f59727 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (61160448 + i)

theorem c59727_0 : rowSum f59727 0 943 = 13493293 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59727) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover59727 (by decide)
  decide +kernel

theorem c59727_1 : rowSum f59727 943 81 = 12703896 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59727) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover59727 (by decide)
  decide +kernel

theorem sum59727 : rowSum f59727 0 1024 = 26197189 :=
  rowSum_append (F := f59727) (lo := 0) (n := 943) (m := 81) (A := 13493293) (B := 12703896) c59727_0 (c59727_1)

theorem h59727 : P.leaf 34 59727 = 26197189 :=
  leaf_weighted (k := 24) (d := 10) (H := 59727) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 59727) (by decide) (by decide +kernel)) sum59727

theorem h24026 : P.leaf 34 24026 = 26197189 :=
  orient24 (v := 59727) (by decide) (by decide +kernel) h59727

theorem cover59743 : P.CoversSplit 24 10 59743 0xfffffffffafa0000fffffffffafa0000f500f50040000000f500f50040000000ffccffccfac800000000000000000000f500f500400000000000000000000000f030f030f0300000f030f030f0300000f000f00050000000f000f000500000002000200020000000000000000000000030003000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 572, 859, 866, 908, 915, 1202, 1308, 1601]) (ps := [(8, [537, 586], [523, 565])]) (by decide +kernel)

noncomputable def f59743 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (61176832 + i)

theorem c59743_0 : rowSum f59743 0 947 = 37038488 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59743) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover59743 (by decide)
  decide +kernel

theorem c59743_1 : rowSum f59743 947 77 = 21893240 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59743) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover59743 (by decide)
  decide +kernel

theorem sum59743 : rowSum f59743 0 1024 = 58931728 :=
  rowSum_append (F := f59743) (lo := 0) (n := 947) (m := 77) (A := 37038488) (B := 21893240) c59743_0 (c59743_1)

theorem h59743 : P.leaf 34 59743 = 58931728 :=
  leaf_weighted (k := 24) (d := 10) (H := 59743) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 59743) (by decide) (by decide +kernel)) sum59743

theorem h24027 : P.leaf 34 24027 = 58931728 :=
  orient24 (v := 59743) (by decide) (by decide +kernel) h59743

theorem cover24028 : P.CoversSplit 24 10 24028 0xff00ff00f000a000ff00ff00f000a000aa00000000000000aa00000000000000cc00cc0080008000cc00cc008000800088000000000000008800000000000000ff00ff00f000a000ff00ff00f000a000aa00000000000000aa000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 472, 516, 858, 916, 1202, 1210, 1601]) (ps := [(18, [867], [1210])]) (by decide +kernel)

theorem c24028_0 : P.sumLeaves 24 24604672 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24028) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover24028 (by decide)
  decide +kernel

theorem contract24028_1 : P.leaf 30 384452 = 0 := by
  exact leaf_contract_zero (ss := [(29, 1, 472), (18, 1, 867), (11, 1, 879), (8, 0, 1266), (20, 1, 531), (21, 1, 537)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c24028_1 : P.sumLeaves 24 24604928 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 384452) rows (by decide) (by decide)).symm.trans contract24028_1

theorem contract24028_2 : P.leaf 30 384453 = 0 := by
  exact leaf_contract_zero (ss := [(29, 1, 472), (18, 1, 867), (11, 1, 879), (8, 0, 1266), (20, 1, 531), (21, 1, 537)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c24028_2 : P.sumLeaves 24 24604992 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 384453) rows (by decide) (by decide)).symm.trans contract24028_2

theorem c24028_3 : P.sumLeaves 24 24605056 574 = 21102560 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24028) (lo := 384) (len := 574) (W := 21102560) check rows elimOK (by decide) (by decide) cover24028 (by decide)
  decide +kernel

theorem c24028_4 : P.sumLeaves 24 24605630 66 = 14412204 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24028) (lo := 958) (len := 66) (W := 14412204) check rows elimOK (by decide) (by decide) cover24028 (by decide)
  decide +kernel

theorem h24028 : P.leaf 34 24028 = 35514764 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 0), (64, 0), (574, 21102560), (66, 14412204)]) (.cons c24028_0 (.cons c24028_1 (.cons c24028_2 (.cons c24028_3 (.cons c24028_4 (.nil)))))) (by decide) (by decide))

theorem cover24029 : P.CoversSplit 24 10 24029 0xfffffffff0f0a0a0fffffffff0f0a0a0ffff000000005050ffff000000005050cccccccc80008000cc00cc0080008000cccc000040004000cc00000040004000ff00ff00f000a000ff33ff33f030a020ff00550000005000ff335511000050000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 516, 858, 865, 916, 1202, 1210, 1259, 1601]) (ps := [(14, [1217], [916])]) (by decide +kernel)

theorem c24029_0 : P.sumLeaves 24 24605696 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24029) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover24029 (by decide)
  decide +kernel

theorem contract24029_1 : P.leaf 30 384468 = 0 := by
  exact leaf_contract_zero (ss := [(11, 1, 879), (8, 0, 1266), (21, 0, 1266), (14, 1, 537), (20, 1, 580), (29, 1, 916)]) (q := 1658) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c24029_1 : P.sumLeaves 24 24605952 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 384468) rows (by decide) (by decide)).symm.trans contract24029_1

theorem contract24029_2 : P.leaf 30 384469 = 0 := by
  exact leaf_contract_zero (ss := [(11, 1, 879), (29, 1, 916), (8, 0, 1266), (21, 0, 1266), (14, 1, 537), (20, 1, 580)]) (q := 1658) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c24029_2 : P.sumLeaves 24 24606016 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 384469) rows (by decide) (by decide)).symm.trans contract24029_2

theorem c24029_3 : P.sumLeaves 24 24606080 379 = 22590396 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24029) (lo := 384) (len := 379) (W := 22590396) check rows elimOK (by decide) (by decide) cover24029 (by decide)
  decide +kernel

theorem c24029_4 : P.sumLeaves 24 24606459 226 = 34737471 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24029) (lo := 763) (len := 226) (W := 34737471) check rows elimOK (by decide) (by decide) cover24029 (by decide)
  decide +kernel

theorem c24029_5 : P.sumLeaves 24 24606685 35 = 25144486 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24029) (lo := 989) (len := 35) (W := 25144486) check rows elimOK (by decide) (by decide) cover24029 (by decide)
  decide +kernel

theorem h24029 : P.leaf 34 24029 = 82472353 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 0), (64, 0), (379, 22590396), (226, 34737471), (35, 25144486)]) (.cons c24029_0 (.cons c24029_1 (.cons c24029_2 (.cons c24029_3 (.cons c24029_4 (.cons c24029_5 (.nil))))))) (by decide) (by decide))

theorem cover24030 : P.CoversSplit 24 10 24030 0xfffffffff0f0a0a0fffffffff0f0a0a0aaaa000000000000aaaa000000000000ccc0ccc080008000cc00cc008000800088800000000000008800000000000000fffffffff0f0a0a0fffffffff0f0a0a0aaaa000000000000aaaa000000000000ccc0ccc080008000cc00cc008000800088000000000000008800000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 516, 858, 865, 1202, 1210, 1259, 1601]) (ps := [(8, [1609], [1266]), (18, [867], [1210])]) (by decide +kernel)

theorem c24030_0 : P.sumLeaves 24 24606720 256 = 3495462 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24030) (lo := 0) (len := 256) (W := 3495462) check rows elimOK (by decide) (by decide) cover24030 (by decide)
  decide +kernel

theorem contract24030_1 : P.leaf 30 384484 = 0 := by
  exact leaf_contract_zero (ss := [(18, 1, 867), (11, 1, 879), (8, 0, 1266), (20, 1, 531), (21, 1, 537), (5, 1, 565)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c24030_1 : P.sumLeaves 24 24606976 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 384484) rows (by decide) (by decide)).symm.trans contract24030_1

theorem contract24030_2 : P.leaf 30 384485 = 0 := by
  exact leaf_contract_zero (ss := [(18, 1, 867), (11, 1, 879), (8, 0, 1266), (20, 1, 531), (21, 1, 537)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c24030_2 : P.sumLeaves 24 24607040 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 384485) rows (by decide) (by decide)).symm.trans contract24030_2

theorem c24030_3 : P.sumLeaves 24 24607104 299 = 28404722 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24030) (lo := 384) (len := 299) (W := 28404722) check rows elimOK (by decide) (by decide) cover24030 (by decide)
  decide +kernel

theorem c24030_4 : P.sumLeaves 24 24607403 312 = 53467779 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24030) (lo := 683) (len := 312) (W := 53467779) check rows elimOK (by decide) (by decide) cover24030 (by decide)
  decide +kernel

theorem c24030_5 : P.sumLeaves 24 24607715 29 = 30121668 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24030) (lo := 995) (len := 29) (W := 30121668) check rows elimOK (by decide) (by decide) cover24030 (by decide)
  decide +kernel

theorem h24030 : P.leaf 34 24030 = 115489631 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 3495462), (64, 0), (64, 0), (299, 28404722), (312, 53467779), (29, 30121668)]) (.cons c24030_0 (.cons c24030_1 (.cons c24030_2 (.cons c24030_3 (.cons c24030_4 (.cons c24030_5 (.nil))))))) (by decide) (by decide))

theorem cover24031 : P.CoversSplit 24 10 24031 0xfffffffff0f0a0a0fffffffff0f0a0a0ffff000000005050ffff000000005050cccccccc80008000cc00cc0080008000cccc000040004000cc00000040004000fffffffff0f0a0a0fffffffff0f0a0a0ffff555500005050ffff555500005050cccccccc80008000cc00cc0080008000cc00440040004000cc00440040004000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 858, 865, 1202, 1210, 1259, 1601]) (ps := [(8, [1609], [1266])]) (by decide +kernel)

theorem contract24031_0 : P.leaf 30 384496 = 0 := by
  exact leaf_contract_zero (ss := [(3, 1, 536), (11, 1, 879), (29, 1, 1259), (8, 0, 1266), (5, 1, 565), (21, 0, 1266), (14, 1, 537), (20, 1, 1272), (27, 1, 1601)]) (q := 1658) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c24031_0 : P.sumLeaves 24 24607744 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 384496) rows (by decide) (by decide)).symm.trans contract24031_0

theorem contract24031_1 : P.leaf 30 384497 = 0 := by
  exact leaf_contract_zero (ss := [(3, 1, 536), (11, 1, 879), (8, 0, 1266), (5, 1, 622), (21, 0, 1266), (14, 1, 537), (20, 1, 1272), (27, 1, 1601), (29, 1, 1609)]) (q := 1658) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c24031_1 : P.sumLeaves 24 24607808 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 384497) rows (by decide) (by decide)).symm.trans contract24031_1

theorem c24031_2 : P.sumLeaves 24 24607872 128 = 7367896 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24031) (lo := 128) (len := 128) (W := 7367896) check rows elimOK (by decide) (by decide) cover24031 (by decide)
  decide +kernel

theorem contract24031_3 : P.leaf 30 384500 = 0 := by
  exact leaf_contract_zero (ss := [(11, 1, 879), (8, 0, 1266), (5, 1, 565), (21, 0, 1266), (14, 1, 537), (20, 1, 1272)]) (q := 1658) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c24031_3 : P.sumLeaves 24 24608000 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 384500) rows (by decide) (by decide)).symm.trans contract24031_3

theorem contract24031_4 : P.leaf 30 384501 = 0 := by
  exact leaf_contract_zero (ss := [(11, 1, 879), (8, 0, 1266), (21, 0, 1266), (14, 1, 537), (20, 1, 1272)]) (q := 1658) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c24031_4 : P.sumLeaves 24 24608064 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 384501) rows (by decide) (by decide)).symm.trans contract24031_4

theorem c24031_5 : P.sumLeaves 24 24608128 242 = 48156102 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24031) (lo := 384) (len := 242) (W := 48156102) check rows elimOK (by decide) (by decide) cover24031 (by decide)
  decide +kernel

theorem c24031_6 : P.sumLeaves 24 24608370 310 = 61457172 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24031) (lo := 626) (len := 310) (W := 61457172) check rows elimOK (by decide) (by decide) cover24031 (by decide)
  decide +kernel

theorem c24031_7 : P.sumLeaves 24 24608680 88 = 99572694 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24031) (lo := 936) (len := 88) (W := 99572694) check rows elimOK (by decide) (by decide) cover24031 (by decide)
  decide +kernel

theorem h24031 : P.leaf 34 24031 = 216553864 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 0), (64, 0), (128, 7367896), (64, 0), (64, 0), (242, 48156102), (310, 61457172), (88, 99572694)]) (.cons c24031_0 (.cons c24031_1 (.cons c24031_2 (.cons c24031_3 (.cons c24031_4 (.cons c24031_5 (.cons c24031_6 (.cons c24031_7 (.nil))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(24011, 24), (24012, 24), (24013, 48), (24015, 24), (24026, 12), (24027, 24), (24028, 48), (24029, 48), (24030, 48), (24031, 48)]

theorem segOK : checkSeg 16 perms 24011 24044 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 24011 24044 348 26687621028 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 26687621028)
    (SegSum.cons (w := 24) h24011 (SegSum.cons (w := 24) h24012 (SegSum.cons (w := 48) h24013 (SegSum.cons (w := 24) h24015 (SegSum.cons (w := 12) h24026 (SegSum.cons (w := 24) h24027 (SegSum.cons (w := 48) h24028 (SegSum.cons (w := 48) h24029 (SegSum.cons (w := 48) h24030 (SegSum.cons (w := 48) h24031 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))) (by decide)

end RACert.S4N1.C0.S74
