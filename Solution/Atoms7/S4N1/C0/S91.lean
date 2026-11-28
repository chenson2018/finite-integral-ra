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

namespace RACert.S4N1.C0.S91

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
  leaf_weighted (k := 24) (d := 10) (H := 65004) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 65004) (by decide) (by decide +kernel)) sum65004

theorem cover65020 : P.CoversSplit 24 10 65020 0xfffffffffaf0f0f0fffffffffaf0f0f0fffffffffaf0f0f0fffffffffaf0f0f0ffc0ffc0fac0f0c0ff00ff00fa00f000ffc0ffc0fac0f0c0ff00ff00fa00f000fffffffffaf0f0f0fffffffffaf0f0f0fffffffffaf0f0f0fffffffffaf0f0f0ffc0ffc0fac0f0c0ff00ff00fa00f000ffc0ffc0fac0f0c0ff00ff00fa00f000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 858, 865]) (by decide +kernel)

noncomputable def f65020 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (66580480 + i)

theorem c65020_0 : rowSum f65020 0 236 = 71266166 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 65020) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65020 (by decide)
  decide +kernel

theorem c65020_1 : rowSum f65020 236 208 = 183945863 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 65020) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65020 (by decide)
  decide +kernel

theorem c65020_2 : rowSum f65020 444 316 = 242525154 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 65020) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65020 (by decide)
  decide +kernel

theorem c65020_3 : rowSum f65020 760 264 = 168723221 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 65020) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65020 (by decide)
  decide +kernel

theorem sum65020 : rowSum f65020 0 1024 = 666460404 :=
  rowSum_append (F := f65020) (lo := 0) (n := 236) (m := 788) (A := 71266166) (B := 595194238) c65020_0 (rowSum_append (F := f65020) (lo := 236) (n := 208) (m := 580) (A := 183945863) (B := 411248375) c65020_1 (rowSum_append (F := f65020) (lo := 444) (n := 316) (m := 264) (A := 242525154) (B := 168723221) c65020_2 (c65020_3)))

theorem h65020 : P.leaf 34 65020 = 666460404 :=
  leaf_weighted (k := 24) (d := 10) (H := 65020) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 65020) (by decide) (by decide +kernel)) sum65020

theorem h65005 : P.leaf 34 65005 = 666460404 :=
  orient24 (v := 65020) (by decide) (by decide +kernel) h65020

theorem cover65532 : P.CoversSplit 24 10 65532 0xfffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafaffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8fffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafaffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473]) (by decide +kernel)

noncomputable def f65532 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (67104768 + i)

theorem c65532_0 : rowSum f65532 0 173 = 102667428 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 65532) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65532 (by decide)
  decide +kernel

theorem c65532_1 : rowSum f65532 173 216 = 246526926 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 65532) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65532 (by decide)
  decide +kernel

theorem c65532_2 : rowSum f65532 389 110 = 401518624 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 65532) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65532 (by decide)
  decide +kernel

theorem c65532_3 : rowSum f65532 499 449 = 383603050 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 65532) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65532 (by decide)
  decide +kernel

theorem c65532_4 : rowSum f65532 948 76 = 158481232 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 65532) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65532 (by decide)
  decide +kernel

theorem sum65532 : rowSum f65532 0 1024 = 1292797260 :=
  rowSum_append (F := f65532) (lo := 0) (n := 173) (m := 851) (A := 102667428) (B := 1190129832) c65532_0 (rowSum_append (F := f65532) (lo := 173) (n := 216) (m := 635) (A := 246526926) (B := 943602906) c65532_1 (rowSum_append (F := f65532) (lo := 389) (n := 110) (m := 525) (A := 401518624) (B := 542084282) c65532_2 (rowSum_append (F := f65532) (lo := 499) (n := 449) (m := 76) (A := 383603050) (B := 158481232) c65532_3 (c65532_4))))

theorem h65532 : P.leaf 34 65532 = 1292797260 :=
  leaf_weighted (k := 24) (d := 10) (H := 65532) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 65532) (by decide) (by decide +kernel)) sum65532

theorem h65007 : P.leaf 34 65007 = 1292797260 :=
  orient32 (v := 65532) (by decide) (by decide +kernel) h65532

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
  leaf_weighted (k := 24) (d := 10) (H := 65023) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 65023) (by decide) (by decide +kernel)) sum65023

def seg : List (ℕ × ℕ) := [(65004, 1), (65005, 4), (65007, 6), (65023, 4)]

theorem segOK : checkSeg 16 perms 65004 65535 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 65004 65535 15 20218106102 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 20218106102)
    (SegSum.cons (w := 1) h65004 (SegSum.cons (w := 4) h65005 (SegSum.cons (w := 6) h65007 (SegSum.cons (w := 4) h65023 (show SegSum (P.leaf 34) [] 0 from rfl))))) (by decide)

end RACert.S4N1.C0.S91
