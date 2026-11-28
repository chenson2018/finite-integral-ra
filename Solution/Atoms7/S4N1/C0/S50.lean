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

namespace RACert.S4N1.C0.S50

open RACert RACert.Problem

theorem cover36779 : P.CoversSplit 24 10 36779 0xfffffffff0f0a0a0fffffffff0f0a0a0fffffffff0f0a0a0fffffffff0f0a0a0cccccccc80008000ff00ff00a000a000cccccccc80008000ff00ff00a000a000fffffffff0f0a0a00000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 916, 1202, 1209, 1258, 1308, 1601]) (ps := [(14, [965], [1272]), (19, [965], [1264])]) (by decide +kernel)

theorem c36779_0 : P.sumLeaves 24 37661696 697 = 7082048 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 36779) (lo := 0) (len := 697) (W := 7082048) check rows elimOK (by decide) (by decide) cover36779 (by decide)
  decide +kernel

theorem c36779_1 : P.sumLeaves 24 37662393 182 = 14926490 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 36779) (lo := 697) (len := 182) (W := 14926490) check rows elimOK (by decide) (by decide) cover36779 (by decide)
  decide +kernel

theorem c36779_2 : P.sumLeaves 24 37662575 136 = 29844574 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 36779) (lo := 879) (len := 136) (W := 29844574) check rows elimOK (by decide) (by decide) cover36779 (by decide)
  decide +kernel

theorem c36779_3 : P.sumLeaves 24 37662711 9 = 7628140 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 36779) (lo := 1015) (len := 9) (W := 7628140) check rows elimOK (by decide) (by decide) cover36779 (by decide)
  decide +kernel

theorem h36779 : P.leaf 34 36779 = 59481252 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(697, 7082048), (182, 14926490), (136, 29844574), (9, 7628140)]) (.cons c36779_0 (.cons c36779_1 (.cons c36779_2 (.cons c36779_3 (.nil))))) (by decide) (by decide))

theorem h8118 : P.leaf 34 8118 = 59481252 :=
  orient25 (v := 36779) (by decide) (by decide +kernel) h36779

theorem cover36795 : P.CoversSplit 24 10 36795 0xfffffffff0f0a0a0fffffffff0f0a0a0fffffffff0f0a0a0fffffffff0f0a0a0cccccccc80008000ff00ff00a000a000cccccccc80008000ff00ff00a000a000fffffffff0f0a0a0fffffffff0f0a0a000000000000000000000000000000000cccccccc80008000ff00ff00a000a00000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 915, 916, 1202, 1209, 1258, 1308, 1601]) (ps := [(8, [1609], [1272]), (14, [965], [1272])]) (by decide +kernel)

theorem c36795_0 : P.sumLeaves 24 37678080 482 = 8677800 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 36795) (lo := 0) (len := 482) (W := 8677800) check rows elimOK (by decide) (by decide) cover36795 (by decide)
  decide +kernel

theorem c36795_1 : P.sumLeaves 24 37678562 268 = 23478332 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 36795) (lo := 482) (len := 268) (W := 23478332) check rows elimOK (by decide) (by decide) cover36795 (by decide)
  decide +kernel

theorem c36795_2 : P.sumLeaves 24 37678830 144 = 34728993 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 36795) (lo := 750) (len := 144) (W := 34728993) check rows elimOK (by decide) (by decide) cover36795 (by decide)
  decide +kernel

theorem c36795_3 : P.sumLeaves 24 37678974 130 = 68943033 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 36795) (lo := 894) (len := 130) (W := 68943033) check rows elimOK (by decide) (by decide) cover36795 (by decide)
  decide +kernel

theorem h36795 : P.leaf 34 36795 = 135828158 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(482, 8677800), (268, 23478332), (144, 34728993), (130, 68943033)]) (.cons c36795_0 (.cons c36795_1 (.cons c36795_2 (.cons c36795_3 (.nil))))) (by decide) (by decide))

theorem h8119 : P.leaf 34 8119 = 135828158 :=
  orient25 (v := 36795) (by decide) (by decide +kernel) h36795

theorem cover8124 : P.CoversSplit 24 10 8124 0xffaaffaaf0a0a0a0ffaaffaaf0a0a0a0aaaaafaa00000000aaaaafaa00000000cc88cc8880008000cc00cc008000800088888c880000000088008c0000000000ff00ff00f000a000ff22ff22f020a020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 517, 916, 1202, 1210, 1258, 1308, 1601]) (by decide +kernel)

noncomputable def f8124 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 24 (8318976 + i)

theorem c8124_0 : rowSum f8124 0 1017 = 51072366 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8124) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover8124 (by decide)
  decide +kernel

theorem c8124_1 : rowSum f8124 1017 7 = 7192904 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8124) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover8124 (by decide)
  decide +kernel

theorem sum8124 : rowSum f8124 0 1024 = 58265270 :=
  rowSum_append (F := f8124) (lo := 0) (n := 1017) (m := 7) (A := 51072366) (B := 7192904) c8124_0 (c8124_1)

theorem h8124 : P.leaf 34 8124 = 58265270 :=
  leaf_weighted (k := 24) (d := 10) (H := 8124) (keep := keep4) (twice := twice4) rows (by decide) (by decide) (bal4) (invRow4 (H := 8124) (by decide) (by decide +kernel)) sum8124

theorem cover8125 : P.CoversSplit 24 10 8125 0xfffffffff5f5a0a0fffffffff5f5a0a0fffffffff5f5a0a0fffffffff5f5a0a0ccffccff80008000cc00cc0080008000ccffccff80008000cc00cc0080008000ff00ff00f500a000ff33ff33f531a020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 517, 916, 1202, 1209, 1210, 1217, 1258, 1308, 1601]) (by decide +kernel)

theorem c8125_0 : P.sumLeaves 24 8320000 655 = 19285833 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8125) (lo := 0) (len := 655) (W := 19285833) check rows elimOK (by decide) (by decide) cover8125 (by decide)
  decide +kernel

theorem c8125_1 : P.sumLeaves 24 8320655 205 = 25297631 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8125) (lo := 655) (len := 205) (W := 25297631) check rows elimOK (by decide) (by decide) cover8125 (by decide)
  decide +kernel

theorem c8125_2 : P.sumLeaves 24 8320860 128 = 48422364 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8125) (lo := 860) (len := 128) (W := 48422364) check rows elimOK (by decide) (by decide) cover8125 (by decide)
  decide +kernel

theorem c8125_3 : P.sumLeaves 24 8320988 36 = 47893070 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8125) (lo := 988) (len := 36) (W := 47893070) check rows elimOK (by decide) (by decide) cover8125 (by decide)
  decide +kernel

theorem h8125 : P.leaf 34 8125 = 140898898 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(655, 19285833), (205, 25297631), (128, 48422364), (36, 47893070)]) (.cons c8125_0 (.cons c8125_1 (.cons c8125_2 (.cons c8125_3 (.nil))))) (by decide) (by decide))

theorem cover8127 : P.CoversSplit 24 10 8127 0xfffffffff5f5a0a0fffffffff5f5a0a0fffffffff5f5a0a0fffffffff5f5a0a0ccffccff80008000cc00cc0080008000ccffccff80008000cc00cc0080008000fffffffff5f5a0a0fffffffff5f5a0a000000000000000000000000000000000ccffccff80008000cc00cc008000800000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 916, 1202, 1209, 1210, 1217, 1258, 1308, 1601]) (by decide +kernel)

noncomputable def f8127 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 24 (8322048 + i)

theorem c8127_0 : rowSum f8127 0 476 = 48185690 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8127) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover8127 (by decide)
  decide +kernel

theorem c8127_1 : rowSum f8127 476 483 = 173507120 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8127) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover8127 (by decide)
  decide +kernel

theorem c8127_2 : rowSum f8127 959 65 = 47978282 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8127) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover8127 (by decide)
  decide +kernel

theorem sum8127 : rowSum f8127 0 1024 = 269671092 :=
  rowSum_append (F := f8127) (lo := 0) (n := 476) (m := 548) (A := 48185690) (B := 221485402) c8127_0 (rowSum_append (F := f8127) (lo := 476) (n := 483) (m := 65) (A := 173507120) (B := 47978282) c8127_1 (c8127_2))

theorem h8127 : P.leaf 34 8127 = 269671092 :=
  leaf_weighted (k := 24) (d := 10) (H := 8127) (keep := keep4) (twice := twice4) rows (by decide) (by decide) (bal4) (invRow4 (H := 8127) (by decide) (by decide +kernel)) sum8127

theorem cover51999 : P.CoversSplit 24 10 51999 0xfffffffffa000a00fffffffffa000a00ffffffffc8000800ffffffffc8000800aa88aa88aa000a002200220022000200aa88aa88880008002200220000000000fffffffffa000a00fffffffffa000a00ffffffffc8000800ffffffffc8000800a080a080a00000002000200020000000a080a080800000002000200000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [516, 523, 565, 572, 866, 879, 1202, 1601]) (by decide +kernel)

noncomputable def f51999 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 24 (53246976 + i)

theorem c51999_0 : rowSum f51999 0 457 = 12175412 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 51999) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover51999 (by decide)
  decide +kernel

theorem c51999_1 : rowSum f51999 457 562 = 49833924 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 51999) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover51999 (by decide)
  decide +kernel

theorem c51999_2 : rowSum f51999 1019 5 = 2312992 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 51999) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover51999 (by decide)
  decide +kernel

theorem sum51999 : rowSum f51999 0 1024 = 64322328 :=
  rowSum_append (F := f51999) (lo := 0) (n := 457) (m := 567) (A := 12175412) (B := 52146916) c51999_0 (rowSum_append (F := f51999) (lo := 457) (n := 562) (m := 5) (A := 49833924) (B := 2312992) c51999_1 (c51999_2))

theorem h51999 : P.leaf 34 51999 = 64322328 :=
  leaf_weighted (k := 24) (d := 10) (H := 51999) (keep := keep4) (twice := twice4) rows (by decide) (by decide) (bal4) (invRow4 (H := 51999) (by decide) (by decide +kernel)) sum51999

theorem h8147 : P.leaf 34 8147 = 64322328 :=
  orient5 (v := 51999) (by decide) (by decide +kernel) h51999

def seg : List (ℕ × ℕ) := [(8118, 48), (8119, 48), (8124, 24), (8125, 48), (8127, 24), (8147, 12)]

theorem segOK : checkSeg 16 perms 8118 8148 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 8118 8148 204 24780339408 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 24780339408)
    (SegSum.cons (w := 48) h8118 (SegSum.cons (w := 48) h8119 (SegSum.cons (w := 24) h8124 (SegSum.cons (w := 48) h8125 (SegSum.cons (w := 24) h8127 (SegSum.cons (w := 12) h8147 (show SegSum (P.leaf 34) [] 0 from rfl))))))) (by decide)

end RACert.S4N1.C0.S50
