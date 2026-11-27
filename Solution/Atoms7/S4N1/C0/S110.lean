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

namespace RACert.S4N1.C0.S110

open RACert RACert.Problem

theorem cover65004 : P.CoversSplit 24 10 65004 0xffffffffeae0a0a0ffffffffeae0a0a0ffffffffeae0a0a0ffffffffeae0a0a0eec0eec0eac0a080cc00cc00c8008000eec0eec0eac0a080cc00cc00c8008000ffffffffeae0a0a0ffffffffeae0a0a0ffffffffeae0a0a0ffffffffeae0a0a0eec0eec0eac0a080cc00cc00c8008000eec0eec0eac0a080cc00cc00c8008000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 858, 865]) (by decide +kernel)

noncomputable def f65004 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (66564096 + i)

theorem c65004_0 : rowSum f65004 0 368 = 53876738 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 65004) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65004 (by decide)
  decide +kernel

theorem c65004_1 : rowSum f65004 368 142 = 128698024 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 65004) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65004 (by decide)
  decide +kernel

theorem c65004_2 : rowSum f65004 510 514 = 149701944 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 65004) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65004 (by decide)
  decide +kernel

theorem sum65004 : rowSum f65004 0 1024 = 332276706 :=
  rowSum_append (F := f65004) (lo := 0) (n := 368) (m := 656) (A := 53876738) (B := 278399968) c65004_0 (rowSum_append (F := f65004) (lo := 368) (n := 142) (m := 514) (A := 128698024) (B := 149701944) c65004_1 (c65004_2))

theorem h65004 : P.leaf 34 65004 = 332276706 :=
  leaf_weighted (k := 24) (d := 10) (H := 65004) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 65004) (by decide) (by decide +kernel)) sum65004

theorem cover65005 : P.CoversSplit 24 10 65005 0xffffffffeee0a0a0ffffffffeee0a0a0ffffffffeee0a0a0ffffffffeee0a0a0ffecffeceee0a0a0ffccffcceec0a080ffecffeceee0a0a0ffccffcceec0a080ffffffffeee0a0a0ffffffffeee0a0a0ffffffffeae0a0a0ffffffffeae0a0a0ffecffeceee0a0a0ffccffcceec0a080ffccffcceac0a080ffccffcceac0a080 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 858, 865, 1217, 1609]) (by decide +kernel)

noncomputable def f65005 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (66565120 + i)

theorem c65005_0 : rowSum f65005 0 290 = 58509540 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 65005) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover65005 (by decide)
  decide +kernel

theorem c65005_1 : rowSum f65005 290 208 = 146175534 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 65005) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover65005 (by decide)
  decide +kernel

theorem c65005_2 : rowSum f65005 498 261 = 176674394 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 65005) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover65005 (by decide)
  decide +kernel

theorem c65005_3 : rowSum f65005 759 224 = 195206450 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 65005) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover65005 (by decide)
  decide +kernel

theorem c65005_4 : rowSum f65005 983 41 = 89894486 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 65005) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover65005 (by decide)
  decide +kernel

theorem sum65005 : rowSum f65005 0 1024 = 666460404 :=
  rowSum_append (F := f65005) (lo := 0) (n := 290) (m := 734) (A := 58509540) (B := 607950864) c65005_0 (rowSum_append (F := f65005) (lo := 290) (n := 208) (m := 526) (A := 146175534) (B := 461775330) c65005_1 (rowSum_append (F := f65005) (lo := 498) (n := 261) (m := 265) (A := 176674394) (B := 285100936) c65005_2 (rowSum_append (F := f65005) (lo := 759) (n := 224) (m := 41) (A := 195206450) (B := 89894486) c65005_3 (c65005_4))))

theorem h65005 : P.leaf 34 65005 = 666460404 :=
  leaf_weighted (k := 24) (d := 10) (H := 65005) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 65005) (by decide) (by decide +kernel)) sum65005

theorem cover65007 : P.CoversSplit 24 10 65007 0xfffffffffefafafafffffffffefafafafffffffffefafafafffffffffefafafaffecffecfee8fae8ffccffccfec8fac8ffecffecfee8fae8ffccffccfec8fac8fffffffffefafafafffffffffefafafafffffffffafafafafffffffffafafafaffecffecfee8fae8ffccffccfec8fac8ffccffccfac8fac8ffccffccfac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 858, 865, 1217, 1609]) (by decide +kernel)

noncomputable def f65007 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (66567168 + i)

theorem c65007_0 : rowSum f65007 0 172 = 100885868 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 65007) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65007 (by decide)
  decide +kernel

theorem c65007_1 : rowSum f65007 172 208 = 260477864 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 65007) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65007 (by decide)
  decide +kernel

theorem c65007_2 : rowSum f65007 380 111 = 303618328 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 65007) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65007 (by decide)
  decide +kernel

theorem c65007_3 : rowSum f65007 491 440 = 451705212 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 65007) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65007 (by decide)
  decide +kernel

theorem c65007_4 : rowSum f65007 931 93 = 176109988 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 65007) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65007 (by decide)
  decide +kernel

theorem sum65007 : rowSum f65007 0 1024 = 1292797260 :=
  rowSum_append (F := f65007) (lo := 0) (n := 172) (m := 852) (A := 100885868) (B := 1191911392) c65007_0 (rowSum_append (F := f65007) (lo := 172) (n := 208) (m := 644) (A := 260477864) (B := 931433528) c65007_1 (rowSum_append (F := f65007) (lo := 380) (n := 111) (m := 533) (A := 303618328) (B := 627815200) c65007_2 (rowSum_append (F := f65007) (lo := 491) (n := 440) (m := 93) (A := 451705212) (B := 176109988) c65007_3 (c65007_4))))

theorem h65007 : P.leaf 34 65007 = 1292797260 :=
  leaf_weighted (k := 24) (d := 10) (H := 65007) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 65007) (by decide) (by decide +kernel)) sum65007

theorem cover65023 : P.CoversSplit 24 10 65023 0xfffffffffffafafafffffffffffafafafffffffffffafafafffffffffffafafafffcfffcfff8faf8ffccffccffc8fac8fffcfffcfff8faf8ffccffccffc8fac8fffffffffffafafafffffffffffafafafffffffffafafafafffffffffafafafafffcfffcfff8faf8ffccffccffc8fac8ffccffccfac8fac8ffccffccfac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [858, 865, 1217, 1609]) (by decide +kernel)

noncomputable def f65023 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (66583552 + i)

theorem c65023_0 : rowSum f65023 0 171 = 246051064 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 65023) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65023 (by decide)
  decide +kernel

theorem c65023_1 : rowSum f65023 171 198 = 480695076 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 65023) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65023 (by decide)
  decide +kernel

theorem c65023_2 : rowSum f65023 369 114 = 553134754 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 65023) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65023 (by decide)
  decide +kernel

theorem c65023_3 : rowSum f65023 483 275 = 672121898 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 65023) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65023 (by decide)
  decide +kernel

theorem c65023_4 : rowSum f65023 758 266 = 413798263 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 65023) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65023 (by decide)
  decide +kernel

theorem sum65023 : rowSum f65023 0 1024 = 2365801055 :=
  rowSum_append (F := f65023) (lo := 0) (n := 171) (m := 853) (A := 246051064) (B := 2119749991) c65023_0 (rowSum_append (F := f65023) (lo := 171) (n := 198) (m := 655) (A := 480695076) (B := 1639054915) c65023_1 (rowSum_append (F := f65023) (lo := 369) (n := 114) (m := 541) (A := 553134754) (B := 1085920161) c65023_2 (rowSum_append (F := f65023) (lo := 483) (n := 275) (m := 266) (A := 672121898) (B := 413798263) c65023_3 (c65023_4))))

theorem h65023 : P.leaf 34 65023 = 2365801055 :=
  leaf_weighted (k := 24) (d := 10) (H := 65023) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 65023) (by decide) (by decide +kernel)) sum65023

def seg : List (ℕ × ℕ) := [(65004, 1), (65005, 4), (65007, 6), (65023, 4)]

theorem segOK : checkSeg 16 perms 65004 65535 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 65004 65535 15 20218106102 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 20218106102)
    (SegSum.cons (w := 1) h65004 (SegSum.cons (w := 4) h65005 (SegSum.cons (w := 6) h65007 (SegSum.cons (w := 4) h65023 (show SegSum (P.leaf 34) [] 0 from rfl))))) (by decide)

end RACert.S4N1.C0.S110
