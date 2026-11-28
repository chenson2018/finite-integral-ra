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

namespace RACert.S4N1.C0.S83

open RACert RACert.Problem

theorem cover26607 : P.CoversSplit 24 10 26607 0xfffffffffafaaaaafffffffffafaaaaafffffffffafaaaaaffff000000000000ffccffccfac8aa88ccccccccc8c88888ffccffccfac8aa88cccc000000000000fffffffffafaaaaaffff0000fafa0000fffffffffafaaaaaffff000000000000ffcc0000fac80000cccc0000c8c80000ffcc0000fac80000cccc000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 1202, 1251, 1259, 1264, 1601]) (by decide +kernel)

noncomputable def f26607 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (27245568 + i)

theorem c26607_0 : rowSum f26607 0 413 = 107275132 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26607) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover26607 (by decide)
  decide +kernel

theorem c26607_1 : rowSum f26607 413 310 = 221542839 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26607) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover26607 (by decide)
  decide +kernel

theorem c26607_2 : rowSum f26607 723 301 = 274523021 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26607) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover26607 (by decide)
  decide +kernel

theorem sum26607 : rowSum f26607 0 1024 = 603340992 :=
  rowSum_append (F := f26607) (lo := 0) (n := 413) (m := 611) (A := 107275132) (B := 496065860) c26607_0 (rowSum_append (F := f26607) (lo := 413) (n := 310) (m := 301) (A := 221542839) (B := 274523021) c26607_1 (c26607_2))

theorem h26607 : P.leaf 34 26607 = 603340992 :=
  leaf_weighted (k := 24) (d := 10) (H := 26607) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 26607) (by decide) (by decide +kernel)) sum26607

theorem cover26623 : P.CoversSplit 24 10 26623 0xfffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaaffccffccfac8aa88ccccccccc8c88888ffccffccfac8aa88ccccccccc8c88888fffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaaffccffccfac8aa88ccccccccc8c88888ffccffccfac8aa88ccccccccc8c88888 :=
  coversSplit check rows (by decide) (by decide) (xs := [860, 915, 1202, 1259, 1601]) (by decide +kernel)

noncomputable def f26623 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (27261952 + i)

theorem c26623_0 : rowSum f26623 0 226 = 168140106 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26623) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover26623 (by decide)
  decide +kernel

theorem c26623_1 : rowSum f26623 226 206 = 264663788 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26623) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover26623 (by decide)
  decide +kernel

theorem c26623_2 : rowSum f26623 432 300 = 466013892 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26623) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover26623 (by decide)
  decide +kernel

theorem c26623_3 : rowSum f26623 732 292 = 477176811 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26623) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover26623 (by decide)
  decide +kernel

theorem sum26623 : rowSum f26623 0 1024 = 1375994597 :=
  rowSum_append (F := f26623) (lo := 0) (n := 226) (m := 798) (A := 168140106) (B := 1207854491) c26623_0 (rowSum_append (F := f26623) (lo := 226) (n := 206) (m := 592) (A := 264663788) (B := 943190703) c26623_1 (rowSum_append (F := f26623) (lo := 432) (n := 300) (m := 292) (A := 466013892) (B := 477176811) c26623_2 (c26623_3)))

theorem h26623 : P.leaf 34 26623 = 1375994597 :=
  leaf_weighted (k := 24) (d := 10) (H := 26623) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 26623) (by decide) (by decide +kernel)) sum26623

theorem cover58572 : P.CoversSplit 24 10 58572 0x80008000cc00800080008000cc00800080008000000000008000800000000000a0a0a0a0eee0a0a080008000cc0080008000800000000000800080000000000080008000800080008000800080008000800080000000000080008000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 516, 522, 536, 573, 858, 865, 872]) (by decide +kernel)

noncomputable def f58572 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (59977728 + i)

theorem c58572_0 : rowSum f58572 0 1024 = 1108112 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 58572) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover58572 (by decide)
  decide +kernel

theorem sum58572 : rowSum f58572 0 1024 = 1108112 :=
  c58572_0

theorem h58572 : P.leaf 34 58572 = 1108112 :=
  leaf_weighted (k := 24) (d := 10) (H := 58572) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 58572) (by decide) (by decide +kernel)) sum58572

theorem h28072 : P.leaf 34 28072 = 1108112 :=
  orient5 (v := 58572) (by decide) (by decide +kernel) h58572

theorem cover58588 : P.CoversSplit 24 10 58588 0x80008000c000800080008000c000800080008000000000008000800000000000a000a000f000a00080008000c0008000a000a00000000000800080000000000080008000c000800080008000c0008000800080000000000080008000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 516, 536, 573, 858, 860, 915, 1202, 1601]) (by decide +kernel)

noncomputable def f58588 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (59994112 + i)

theorem c58588_0 : rowSum f58588 0 1024 = 8155784 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 58588) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover58588 (by decide)
  decide +kernel

theorem sum58588 : rowSum f58588 0 1024 = 8155784 :=
  c58588_0

theorem h58588 : P.leaf 34 58588 = 8155784 :=
  leaf_weighted (k := 24) (d := 10) (H := 58588) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 58588) (by decide) (by decide +kernel)) sum58588

theorem h28073 : P.leaf 34 28073 = 8155784 :=
  orient24 (v := 58588) (by decide) (by decide +kernel) h58588

theorem cover28075 : P.CoversSplit 24 10 28075 0xaa000000aa0000000000000000000000aa000000000000000000000000000000aa000000aa0000000000000000000000aa000000000000000000000000000000aa000000aa0000000000000000000000aa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 858, 865, 1202, 1210, 1259, 1601]) (by decide +kernel)

noncomputable def f28075 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (28748800 + i)

theorem c28075_0 : rowSum f28075 0 1024 = 36762444 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 28075) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover28075 (by decide)
  decide +kernel

theorem sum28075 : rowSum f28075 0 1024 = 36762444 :=
  c28075_0

theorem h28075 : P.leaf 34 28075 = 36762444 :=
  leaf_weighted (k := 24) (d := 10) (H := 28075) (keep := keep5) (twice := twice5) rows (by decide) (by decide) (bal5) (invRow5 (H := 28075) (by decide) (by decide +kernel)) sum28075

theorem cover28076 : P.CoversSplit 24 10 28076 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [472]) (by decide +kernel)

theorem h28076 : P.leaf 34 28076 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 28076) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 28076) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover28076 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover28077 : P.CoversSplit 24 10 28077 0xaa000000ba00f0000000000000000000aa000000000000000000000000000000aa000000ba00f0000000000000000000aa000000000000000000000000000000aa000000ba00f0000000000000000000aa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 517, 522, 858, 865, 915, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c28077_0 : P.sumLeaves 24 28750848 1024 = 15834606 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28077) (lo := 0) (len := 1024) (W := 15834606) check rows elimOK (by decide) (by decide) cover28077 (by decide)
  decide +kernel

theorem h28077 : P.leaf 34 28077 = 15834606 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 15834606)]) (.cons c28077_0 (.nil)) (by decide) (by decide))

theorem cover28079 : P.CoversSplit 24 10 28079 0xaa000000aa0000000000000000000000aa000000000000000000000000000000aa000000aa0000000000000000000000aa000000000000000000000000000000aa000000aa0000000000000000000000aa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 858, 865, 1202, 1210, 1259, 1601]) (by decide +kernel)

noncomputable def f28079 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (28752896 + i)

theorem c28079_0 : rowSum f28079 0 1024 = 42132004 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 28079) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover28079 (by decide)
  decide +kernel

theorem sum28079 : rowSum f28079 0 1024 = 42132004 :=
  c28079_0

theorem h28079 : P.leaf 34 28079 = 42132004 :=
  leaf_weighted (k := 24) (d := 10) (H := 28079) (keep := keep5) (twice := twice5) rows (by decide) (by decide) (bal5) (invRow5 (H := 28079) (by decide) (by decide +kernel)) sum28079

theorem cover59100 : P.CoversSplit 24 10 59100 0xfca9fca9f8a8a0a0fca9fca9f8a8a0a0fca9fca9c8008000fca9fca9c8008000fc88fc88f888a080cc00cc00c8008000fc88fc88c8008000cc00cc00c8008000fca9fca9f8a8a0a0fca9fca9f8a8a0a0fca9fca9c8008000fca9fca9c8008000a080a080a080a0808000800080008000a080a080900880008000800080008000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 536, 872, 1202, 1601]) (by decide +kernel)

noncomputable def f59100 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 24 (60518400 + i)

theorem c59100_0 : rowSum f59100 0 485 = 45160770 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59100) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover59100 (by decide)
  decide +kernel

theorem c59100_1 : rowSum f59100 485 539 = 100473912 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59100) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover59100 (by decide)
  decide +kernel

theorem sum59100 : rowSum f59100 0 1024 = 145634682 :=
  rowSum_append (F := f59100) (lo := 0) (n := 485) (m := 539) (A := 45160770) (B := 100473912) c59100_0 (c59100_1)

theorem h59100 : P.leaf 34 59100 = 145634682 :=
  leaf_weighted (k := 24) (d := 10) (H := 59100) (keep := keep4) (twice := twice4) rows (by decide) (by decide) (bal4) (invRow4 (H := 59100) (by decide) (by decide +kernel)) sum59100

theorem h28090 : P.leaf 34 28090 = 145634682 :=
  orient5 (v := 59100) (by decide) (by decide +kernel) h59100

theorem cover58591 : P.CoversSplit 24 10 58591 0xfffffffffffaa0a0fffffffffffaa0a0fffffffffffaa0a0fffffffffffaa0a0fffcfffcfff8a0a0cc00cc00cc008000fffcfffcfff8a0a0cc00cc00cc008000fffffffffffaa0a0fffffffffffaa0a0fffffffffafaa0a0fffffffffafaa0a0fffcfffcfff8a0a0cc00cc00cc008000ffccffccfac8a080cc00cc00c8008000 :=
  coversSplit check rows (by decide) (by decide) (xs := [516, 573, 858, 865, 1202, 1217, 1601, 1609]) (by decide +kernel)

noncomputable def f58591 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (59997184 + i)

theorem c58591_0 : rowSum f58591 0 252 = 25816622 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 58591) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover58591 (by decide)
  decide +kernel

theorem c58591_1 : rowSum f58591 252 216 = 82387256 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 58591) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover58591 (by decide)
  decide +kernel

theorem c58591_2 : rowSum f58591 468 464 = 160344596 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 58591) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover58591 (by decide)
  decide +kernel

theorem c58591_3 : rowSum f58591 932 92 = 90851680 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 58591) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover58591 (by decide)
  decide +kernel

theorem sum58591 : rowSum f58591 0 1024 = 359400154 :=
  rowSum_append (F := f58591) (lo := 0) (n := 252) (m := 772) (A := 25816622) (B := 333583532) c58591_0 (rowSum_append (F := f58591) (lo := 252) (n := 216) (m := 556) (A := 82387256) (B := 251196276) c58591_1 (rowSum_append (F := f58591) (lo := 468) (n := 464) (m := 92) (A := 160344596) (B := 90851680) c58591_2 (c58591_3)))

theorem h58591 : P.leaf 34 58591 = 359400154 :=
  leaf_weighted (k := 24) (d := 10) (H := 58591) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 58591) (by decide) (by decide +kernel)) sum58591

theorem h28091 : P.leaf 34 28091 = 359400154 :=
  orient24 (v := 58591) (by decide) (by decide +kernel) h58591

theorem cover40422 : P.CoversSplit 24 10 40422 0xff00ff00fa00fa000000000000000000ff000000000000000000000000000000ee0cee0cea08ea080000000000000000ee0c0000000000000000000000000000ff00ff00fa00fa000000000000000000ff0005000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 472, 515, 522, 858, 865, 1202, 1209, 1258, 1601]) (by decide +kernel)

theorem c40422_0 : P.sumLeaves 24 41392128 1002 = 31230533 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 40422) (lo := 0) (len := 1002) (W := 31230533) check rows elimOK (by decide) (by decide) cover40422 (by decide)
  decide +kernel

theorem c40422_1 : P.sumLeaves 24 41393130 22 = 15026148 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 40422) (lo := 1002) (len := 22) (W := 15026148) check rows elimOK (by decide) (by decide) cover40422 (by decide)
  decide +kernel

theorem h40422 : P.leaf 34 40422 = 46256681 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1002, 31230533), (22, 15026148)]) (.cons c40422_0 (.cons c40422_1 (.nil))) (by decide) (by decide))

theorem h28092 : P.leaf 34 28092 = 46256681 :=
  orient4 (v := 40422) (by decide) (by decide +kernel) h40422

theorem cover40423 : P.CoversSplit 24 10 40423 0xff00ff00fa00fa000000000000000000ff000000000000000000000000000000ff00ff00fa00fa000000000000000000ff000000000000000000000000000000ff00ff00fa00fa000000000000000000ff0005000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [472, 515, 522, 858, 865, 1202, 1209, 1258, 1601]) (by decide +kernel)

theorem c40423_0 : P.sumLeaves 24 41393152 1002 = 74942228 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 40423) (lo := 0) (len := 1002) (W := 74942228) check rows elimOK (by decide) (by decide) cover40423 (by decide)
  decide +kernel

theorem c40423_1 : P.sumLeaves 24 41394154 22 = 28110286 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 40423) (lo := 1002) (len := 22) (W := 28110286) check rows elimOK (by decide) (by decide) cover40423 (by decide)
  decide +kernel

theorem h40423 : P.leaf 34 40423 = 103052514 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1002, 74942228), (22, 28110286)]) (.cons c40423_0 (.cons c40423_1 (.nil))) (by decide) (by decide))

theorem h28093 : P.leaf 34 28093 = 103052514 :=
  orient4 (v := 40423) (by decide) (by decide +kernel) h40423

def seg : List (ℕ × ℕ) := [(26607, 24), (26623, 8), (28072, 6), (28073, 24), (28075, 24), (28076, 24), (28077, 48), (28079, 24), (28090, 12), (28091, 24), (28092, 48), (28093, 48)]

theorem segOK : checkSeg 16 perms 26607 28094 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 26607 28094 314 45884117152 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 45884117152)
    (SegSum.cons (w := 24) h26607 (SegSum.cons (w := 8) h26623 (SegSum.cons (w := 6) h28072 (SegSum.cons (w := 24) h28073 (SegSum.cons (w := 24) h28075 (SegSum.cons (w := 24) h28076 (SegSum.cons (w := 48) h28077 (SegSum.cons (w := 24) h28079 (SegSum.cons (w := 12) h28090 (SegSum.cons (w := 24) h28091 (SegSum.cons (w := 48) h28092 (SegSum.cons (w := 48) h28093 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))) (by decide)

end RACert.S4N1.C0.S83
