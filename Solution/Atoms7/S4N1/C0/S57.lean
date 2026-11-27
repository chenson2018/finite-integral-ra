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

namespace RACert.S4N1.C0.S57

open RACert RACert.Problem

theorem cover8117 : P.CoversSplit 24 10 8117 0xfffffffff5f5a0a0fffffffff5f5a0a0fffffffff5f5a0a0fffffffff5f5a0a0ccffccff80008000cc00cc0080008000ccffccff80008000cc00cc0080008000ff00ff00f500a000ff33ff33f531a020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 517, 916, 1202, 1209, 1210, 1217, 1258, 1308, 1601]) (by decide +kernel)

theorem c8117_0 : P.sumLeaves 24 8311808 655 = 7341554 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8117) (lo := 0) (len := 655) (W := 7341554) check rows elimOK (by decide) (by decide) cover8117 (by decide)
  decide +kernel

theorem c8117_1 : P.sumLeaves 24 8312463 205 = 7774349 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8117) (lo := 655) (len := 205) (W := 7774349) check rows elimOK (by decide) (by decide) cover8117 (by decide)
  decide +kernel

theorem c8117_2 : P.sumLeaves 24 8312668 128 = 15527278 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8117) (lo := 860) (len := 128) (W := 15527278) check rows elimOK (by decide) (by decide) cover8117 (by decide)
  decide +kernel

theorem c8117_3 : P.sumLeaves 24 8312796 36 = 18581010 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8117) (lo := 988) (len := 36) (W := 18581010) check rows elimOK (by decide) (by decide) cover8117 (by decide)
  decide +kernel

theorem h8117 : P.leaf 34 8117 = 49224191 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(655, 7341554), (205, 7774349), (128, 15527278), (36, 18581010)]) (.cons c8117_0 (.cons c8117_1 (.cons c8117_2 (.cons c8117_3 (.nil))))) (by decide) (by decide))

theorem cover8118 : P.CoversSplit 24 10 8118 0xfffffffff5f5a0a0fffffffff5f5a0a0aaaaaaaa0000a0a0aaaaaaaa00000000ccffccff80008000cc00cc008000800088aa88aa000080008800880000000000fffffffff5f5a0a0fffffffff5f5a0a000000000000000000000000000000000ccffccff80008000cc00cc008000800000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 517, 916, 1202, 1209, 1210, 1258, 1308, 1601]) (ps := [(5, [524], [517]), (8, [531], [517])]) (by decide +kernel)

theorem c8118_0 : P.sumLeaves 24 8312832 476 = 5075316 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8118) (lo := 0) (len := 476) (W := 5075316) check rows elimOK (by decide) (by decide) cover8118 (by decide)
  decide +kernel

theorem c8118_1 : P.sumLeaves 24 8313308 339 = 13039110 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8118) (lo := 476) (len := 339) (W := 13039110) check rows elimOK (by decide) (by decide) cover8118 (by decide)
  decide +kernel

theorem c8118_2 : P.sumLeaves 24 8313647 180 = 20176974 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8118) (lo := 815) (len := 180) (W := 20176974) check rows elimOK (by decide) (by decide) cover8118 (by decide)
  decide +kernel

theorem c8118_3 : P.sumLeaves 24 8313827 29 = 21189852 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8118) (lo := 995) (len := 29) (W := 21189852) check rows elimOK (by decide) (by decide) cover8118 (by decide)
  decide +kernel

theorem h8118 : P.leaf 34 8118 = 59481252 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(476, 5075316), (339, 13039110), (180, 20176974), (29, 21189852)]) (.cons c8118_0 (.cons c8118_1 (.cons c8118_2 (.cons c8118_3 (.nil))))) (by decide) (by decide))

theorem cover8119 : P.CoversSplit 24 10 8119 0xfffffffff5f5a0a0fffffffff5f5a0a0fffffffff5f5a0a0fffffffff5f5a0a0ccffccff80008000cc00cc0080008000ccffccff80008000cc00cc0080008000fffffffff5f5a0a0fffffffff5f5a0a000000000000000000000000000000000ccffccff80008000cc00cc008000800000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 916, 1202, 1209, 1210, 1217, 1258, 1308, 1601]) (by decide +kernel)

theorem c8119_0 : P.sumLeaves 24 8313856 476 = 10985502 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8119) (lo := 0) (len := 476) (W := 10985502) check rows elimOK (by decide) (by decide) cover8119 (by decide)
  decide +kernel

theorem c8119_1 : P.sumLeaves 24 8314332 276 = 23689907 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8119) (lo := 476) (len := 276) (W := 23689907) check rows elimOK (by decide) (by decide) cover8119 (by decide)
  decide +kernel

theorem c8119_2 : P.sumLeaves 24 8314608 132 = 15458452 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8119) (lo := 752) (len := 132) (W := 15458452) check rows elimOK (by decide) (by decide) cover8119 (by decide)
  decide +kernel

theorem c8119_3 : P.sumLeaves 24 8314740 128 = 66025941 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8119) (lo := 884) (len := 128) (W := 66025941) check rows elimOK (by decide) (by decide) cover8119 (by decide)
  decide +kernel

theorem c8119_4 : P.sumLeaves 24 8314868 12 = 19668356 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8119) (lo := 1012) (len := 12) (W := 19668356) check rows elimOK (by decide) (by decide) cover8119 (by decide)
  decide +kernel

theorem h8119 : P.leaf 34 8119 = 135828158 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(476, 10985502), (276, 23689907), (132, 15458452), (128, 66025941), (12, 19668356)]) (.cons c8119_0 (.cons c8119_1 (.cons c8119_2 (.cons c8119_3 (.cons c8119_4 (.nil)))))) (by decide) (by decide))

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
  leaf_weighted (k := 24) (d := 10) (H := 8124) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 8124) (by decide) (by decide +kernel)) sum8124

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

def seg : List (ℕ × ℕ) := [(8117, 48), (8118, 48), (8119, 48), (8124, 24), (8125, 48)]

theorem segOK : checkSeg 16 perms 8117 8127 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 8117 8127 216 19899126432 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 19899126432)
    (SegSum.cons (w := 48) h8117 (SegSum.cons (w := 48) h8118 (SegSum.cons (w := 48) h8119 (SegSum.cons (w := 24) h8124 (SegSum.cons (w := 48) h8125 (show SegSum (P.leaf 34) [] 0 from rfl)))))) (by decide)

end RACert.S4N1.C0.S57
