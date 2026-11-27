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

namespace RACert.S4N1.C0.S56

open RACert RACert.Problem

theorem cover8060 : P.CoversSplit 24 10 8060 0xfffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0cc00cc0080008000cc00cc0080008000cc00cc0080008000cc00cc0080008000cc00cc00c8008000cc33cc33c8328020cc00cc00c8008000cc33cc33c82080200000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 572, 916, 1209, 1210, 1601]) (ps := [(8, [1217], [572]), (14, [1217], [916])]) (by decide +kernel)

noncomputable def f8060 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 24 (8253440 + i)

theorem c8060_0 : rowSum f8060 0 801 = 13034825 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8060) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8060 (by decide)
  decide +kernel

theorem c8060_1 : rowSum f8060 801 201 = 47170930 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8060) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8060 (by decide)
  decide +kernel

theorem c8060_2 : rowSum f8060 1002 22 = 22356890 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8060) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8060 (by decide)
  decide +kernel

theorem sum8060 : rowSum f8060 0 1024 = 82562645 :=
  rowSum_append (F := f8060) (lo := 0) (n := 801) (m := 223) (A := 13034825) (B := 69527820) c8060_0 (rowSum_append (F := f8060) (lo := 801) (n := 201) (m := 22) (A := 47170930) (B := 22356890) c8060_1 (c8060_2))

theorem h8060 : P.leaf 34 8060 = 82562645 :=
  leaf_weighted (k := 24) (d := 10) (H := 8060) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 8060) (by decide) (by decide +kernel)) sum8060

theorem cover8061 : P.CoversSplit 24 10 8061 0xffffffffffffa0a0ffffffffffffa0a0ffffffffffffa0a0ffffffffffffa0a0cc33cc3380008000cc00cc0080008000cc33cc3380008000cc00cc0080008000cc00cc00cc008000cc33cc33cc338020cc00cc00c8008000cc33cc33c82080200000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 572, 916, 1209, 1210, 1217, 1258, 1601]) (ps := [(8, [1217], [572]), (14, [1217], [916])]) (by decide +kernel)

noncomputable def f8061 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 24 (8254464 + i)

theorem c8061_0 : rowSum f8061 0 757 = 19738986 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8061) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8061 (by decide)
  decide +kernel

theorem c8061_1 : rowSum f8061 757 190 = 59697108 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8061) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8061 (by decide)
  decide +kernel

theorem c8061_2 : rowSum f8061 947 77 = 67455772 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8061) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8061 (by decide)
  decide +kernel

theorem sum8061 : rowSum f8061 0 1024 = 146891866 :=
  rowSum_append (F := f8061) (lo := 0) (n := 757) (m := 267) (A := 19738986) (B := 127152880) c8061_0 (rowSum_append (F := f8061) (lo := 757) (n := 190) (m := 77) (A := 59697108) (B := 67455772) c8061_1 (c8061_2))

theorem h8061 : P.leaf 34 8061 = 146891866 :=
  leaf_weighted (k := 24) (d := 10) (H := 8061) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 8061) (by decide) (by decide +kernel)) sum8061

theorem cover8062 : P.CoversSplit 24 10 8062 0xffffffffffffa0a0ffffffffffffa0a0ffffffffffffa0a0ffffffffffffa0a0cc33cc3380008000cc00cc0080008000cc33cc3380008000cc00cc0080008000ffffffffffffa0a0ffffffffffffa0a0fffffffffafaa0a0fffffffffafaa0a00000000000000000cc00cc0080008000cc33cc3380008000cc00cc0080008000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 572, 1209, 1210, 1217, 1258, 1601, 1609]) (by decide +kernel)

noncomputable def f8062 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 24 (8255488 + i)

theorem c8062_0 : rowSum f8062 0 403 = 9057456 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8062) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8062 (by decide)
  decide +kernel

theorem c8062_1 : rowSum f8062 403 344 = 29764378 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8062) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8062 (by decide)
  decide +kernel

theorem c8062_2 : rowSum f8062 747 196 = 80386892 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8062) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8062 (by decide)
  decide +kernel

theorem c8062_3 : rowSum f8062 943 81 = 105943074 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8062) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8062 (by decide)
  decide +kernel

theorem sum8062 : rowSum f8062 0 1024 = 225151800 :=
  rowSum_append (F := f8062) (lo := 0) (n := 403) (m := 621) (A := 9057456) (B := 216094344) c8062_0 (rowSum_append (F := f8062) (lo := 403) (n := 344) (m := 277) (A := 29764378) (B := 186329966) c8062_1 (rowSum_append (F := f8062) (lo := 747) (n := 196) (m := 81) (A := 80386892) (B := 105943074) c8062_2 (c8062_3)))

theorem h8062 : P.leaf 34 8062 = 225151800 :=
  leaf_weighted (k := 24) (d := 10) (H := 8062) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 8062) (by decide) (by decide +kernel)) sum8062

theorem cover8063 : P.CoversSplit 24 10 8063 0xffffffffffffa0a0ffffffffffffa0a0ffffffffffffa0a0ffffffffffffa0a0cc33cc3380008000cc00cc0080008000cc33cc3380008000cc00cc0080008000ffffffffffffa0a0ffffffffffffa0a0fffffffffafaa0a0fffffffffafaa0a00000000000000000cc00cc0080008000cc33cc3380008000cc00cc0080008000 :=
  coversSplit check rows (by decide) (by decide) (xs := [572, 1209, 1210, 1217, 1258, 1601, 1609]) (by decide +kernel)

noncomputable def f8063 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 24 (8256512 + i)

theorem c8063_0 : rowSum f8063 0 403 = 17985487 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8063) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8063 (by decide)
  decide +kernel

theorem c8063_1 : rowSum f8063 403 344 = 47347287 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8063) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8063 (by decide)
  decide +kernel

theorem c8063_2 : rowSum f8063 747 196 = 154730925 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8063) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8063 (by decide)
  decide +kernel

theorem c8063_3 : rowSum f8063 943 81 = 140259813 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8063) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover8063 (by decide)
  decide +kernel

theorem sum8063 : rowSum f8063 0 1024 = 360323512 :=
  rowSum_append (F := f8063) (lo := 0) (n := 403) (m := 621) (A := 17985487) (B := 342338025) c8063_0 (rowSum_append (F := f8063) (lo := 403) (n := 344) (m := 277) (A := 47347287) (B := 294990738) c8063_1 (rowSum_append (F := f8063) (lo := 747) (n := 196) (m := 81) (A := 154730925) (B := 140259813) c8063_2 (c8063_3)))

theorem h8063 : P.leaf 34 8063 = 360323512 :=
  leaf_weighted (k := 24) (d := 10) (H := 8063) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 8063) (by decide) (by decide +kernel)) sum8063

theorem cover8115 : P.CoversSplit 24 10 8115 0xfffffffff5f5a0a0fffffffff5f5a0a0fffffffff5f5a0a0fffffffff5f5a0a0ccffccff80008000cc00cc0080008000ccffccff80008000cc00cc0080008000fffffffff5f5a0a0fffffffff5f5a0a000000000000000000000000000000000ccffccff80008000cc00cc008000800000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 916, 1202, 1209, 1210, 1217, 1258, 1308, 1601]) (by decide +kernel)

noncomputable def f8115 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 24 (8309760 + i)

theorem c8115_0 : rowSum f8115 0 476 = 7823658 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8115) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover8115 (by decide)
  decide +kernel

theorem c8115_1 : rowSum f8115 476 483 = 31685370 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8115) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover8115 (by decide)
  decide +kernel

theorem c8115_2 : rowSum f8115 959 65 = 13737272 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8115) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover8115 (by decide)
  decide +kernel

theorem sum8115 : rowSum f8115 0 1024 = 53246300 :=
  rowSum_append (F := f8115) (lo := 0) (n := 476) (m := 548) (A := 7823658) (B := 45422642) c8115_0 (rowSum_append (F := f8115) (lo := 476) (n := 483) (m := 65) (A := 31685370) (B := 13737272) c8115_1 (c8115_2))

theorem h8115 : P.leaf 34 8115 = 53246300 :=
  leaf_weighted (k := 24) (d := 10) (H := 8115) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 8115) (by decide) (by decide +kernel)) sum8115

theorem cover8116 : P.CoversSplit 24 10 8116 0xffaaffaaf0a0a0a0ffaaffaaf0a0a0a0aaaaaaaa0000a0a0aaaaaaaa00000000cc88cc8880008000cc00cc008000800088888888000080008800880000000000ff00ff00f000a000ff22ff22f020a020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 517, 916, 1202, 1210, 1258, 1308, 1601]) (ps := [(5, [524], [517]), (8, [531], [517])]) (by decide +kernel)

theorem c8116_0 : P.sumLeaves 24 8310784 819 = 1907533 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8116) (lo := 0) (len := 819) (W := 1907533) check rows elimOK (by decide) (by decide) cover8116 (by decide)
  decide +kernel

theorem c8116_1 : P.sumLeaves 24 8311603 205 = 5328658 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8116) (lo := 819) (len := 205) (W := 5328658) check rows elimOK (by decide) (by decide) cover8116 (by decide)
  decide +kernel

theorem h8116 : P.leaf 34 8116 = 7236191 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(819, 1907533), (205, 5328658)]) (.cons c8116_0 (.cons c8116_1 (.nil))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(8060, 24), (8061, 24), (8062, 24), (8063, 24), (8115, 12), (8116, 48)]

theorem segOK : checkSeg 16 perms 8060 8117 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 8060 8117 156 20544608520 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 20544608520)
    (SegSum.cons (w := 24) h8060 (SegSum.cons (w := 24) h8061 (SegSum.cons (w := 24) h8062 (SegSum.cons (w := 24) h8063 (SegSum.cons (w := 12) h8115 (SegSum.cons (w := 48) h8116 (show SegSum (P.leaf 34) [] 0 from rfl))))))) (by decide)

end RACert.S4N1.C0.S56
